#!/usr/bin/python -u

import sys
import os
import os.path
import grp
import pwd
import re
import tempfile
import tarfile
import pprint
import difflib
import shutil
import gzip
import bz2
import lzma # pyliblzma
import subprocess
import argparse
import errno
import glob
import string
from email.mime.text import MIMEText
from email.header import Header
from email.utils import formataddr
import json
import xmlrpclib
try:
    from cStringIO import StringIO
except ImportError:
    from StringIO import StringIO

import urlparse
import urllib2

script_path = os.path.realpath(os.path.abspath(sys.argv[0]))
script_dir = os.path.dirname(script_path) + '/git'

sys.path.insert(0, '/home/admin/bin/git')
sys.path.insert(0, script_dir)

# Lives inside gitadmin-bin
import semi_rdf

DEBUG=True

BUGZILLARPC=True

# Protection, only ovitters should be using debug mode:
if not os.environ['USER'] in ('ovitters', 'olav'):
    DEBUG=False

GROUP='ftpadmin'
re_file = re.compile(r'^(?P<module>.*?)[_-](?:(?P<oldversion>([0-9]+[\.])+[0-9]+)-)?(?P<version>(?:(?:[0-9]+\.)*|(?:[0-9]+\-)*)[0-9]+)\.(?P<format>(?:tar\.|diff\.)?[a-z][a-z0-9]*)$')
re_majmin = re.compile(r'^([0-9]+\.[0-9]+).*')
re_version = re.compile(r'([-.]|\d+|[^-.\d]+)')
re_who = re.compile(r' <[^>]+>$')
re_whitespace = re.compile("\s+")

SECTIONS = [
        'sources',
]
DEFAULT_SECTION='sources'
SUITES = [
        'core',
        'apps',
        'platform',
        'desktop',
        'bindings',
        'admin',
        'devtools',
        'mobile',
]
DEFAULT_SUITE=SUITES[0]

def version_cmp(a, b):
    """Compares two versions

    Returns
      -1 if a < b
      0  if a == b
      1  if a > b

    Logic from Bugzilla::Install::Util::vers_cmp"""
    A = re_version.findall(a.lstrip('0'))
    B = re_version.findall(b.lstrip('0'))

    while A and B:
        a = A.pop(0)
        b = B.pop(0)

        if a == b:
            continue
        elif a == '-':
            return -1
        elif b == '-':
            return 1
        elif a == '.':
            return -1
        elif b == '.':
            return 1
        elif a.isdigit() and b.isdigit():
            c = cmp(a, b) if (a.startswith('0') or b.startswith('0')) else cmp(int(a, 10), int(b, 10))
            if c:
                return c
        else:
            c = cmp(a.upper(), b.upper())
            if c:
                return c

    return cmp(len(A), len(B))

def get_latest_version(versions, max_version=None):
    """Gets the latest version number

    if max_version is specified, gets the latest version number before
    max_version"""
    latest = None
    for version in versions:
        if ( latest is None or version_cmp(version, latest) > 0 ) \
           and ( max_version is None or version_cmp(version, max_version) < 0 ):
            latest = version
    return latest

def human_size(size):
    suffixes = [("",2**10), ("K",2**20), ("M",2**30), ("G",2**40), ("T",2**50)]

    for suf, lim in suffixes:
        if size < lim:
            break

    sizediv = size/float(lim/2**10)
    if suf == "":
        fmt = "%0.0f%s"
    elif sizediv > 100:
        fmt = "%0.0f%s"
    elif sizediv > 10:
        fmt = "%0.1f%s"
    else:
        fmt = "%0.2f%s"

    return fmt % (size/float(lim/2**10), suf)

def makedirs_chown(name, mode=0777, uid=-1, gid=-1):
    """Like os.makedirs, but also does a chown
    """
    head, tail = os.path.split(name)
    if not tail:
        head, tail = os.path.split(head)
    if head and tail and not os.path.exists(head):
        try:
            makedirs_chown(head, mode, uid, gid)
        except OSError, e:
            # be happy if someone already created the path
            if e.errno != errno.EEXIST:
                raise
        if tail == os.path.curdir:           # xxx/newdir/. exists if xxx/newdir exists
            return
    os.mkdir(name, mode)
    os.chown(name, uid, gid)

def line_input (file):
    for line in file:
        if line[-1] == '\n':
            yield line[:-1]
        else:
            yield line

class _LZMAProxy(object):
    """Small proxy class that enables external file object
       support for "r:lzma" and "w:lzma" modes. This is actually
       a workaround for a limitation in lzma module's LZMAFile
       class which (unlike gzip.GzipFile) has no support for
       a file object argument.
    """

    blocksize = 16 * 1024

    def __init__(self, fileobj, mode):
        self.fileobj = fileobj
        self.mode = mode
        self.name = getattr(self.fileobj, "name", None)
        self.init()

    def init(self):
#        import lzma
        self.pos = 0
        if self.mode == "r":
            self.lzmaobj = lzma.LZMADecompressor()
            self.fileobj.seek(0)
            self.buf = ""
        else:
            self.lzmaobj = lzma.LZMACompressor()

    def read(self, size):
        b = [self.buf]
        x = len(self.buf)
        while x < size:
            raw = self.fileobj.read(self.blocksize)
            if not raw:
                break
            try:
                data = self.lzmaobj.decompress(raw)
            except EOFError:
                break
            b.append(data)
            x += len(data)
        self.buf = "".join(b)

        buf = self.buf[:size]
        self.buf = self.buf[size:]
        self.pos += len(buf)
        return buf

    def seek(self, pos):
        if pos < self.pos:
            self.init()
        self.read(pos - self.pos)


class XzTarFile(tarfile.TarFile):

    OPEN_METH = tarfile.TarFile.OPEN_METH.copy()
    OPEN_METH["xz"] = "xzopen"

    @classmethod
    def xzopen(cls, name, mode="r", fileobj=None, **kwargs):
        """Open gzip compressed tar archive name for reading or writing.
           Appending is not allowed.
        """
        if len(mode) > 1 or mode not in "rw":
            raise ValueError("mode must be 'r' or 'w'")

        if fileobj is not None:
            fileobj = _LMZAProxy(fileobj, mode)
        else:
            fileobj = lzma.LZMAFile(name, mode)

        try:
            # lzma doesn't immediately return an error
            # try and read a bit of data to determine if it is a valid xz file
            fileobj.read(_LZMAProxy.blocksize)
            fileobj.seek(0)
            t = cls.taropen(name, mode, fileobj, **kwargs)
        except IOError:
            raise tarfile.ReadError("not a xz file")
        except lzma.error:
            raise tarfile.ReadError("not a xz file")
        t._extfileobj = False
        return t

if not hasattr(tarfile.TarFile, 'xzopen'):
    tarfile.open = XzTarFile.open


class SetEncoder(json.JSONEncoder):
    def default(self, obj):
       if isinstance(obj, set):
          return list(obj)
       return json.JSONEncoder.default(self, obj)


class BasicInfo(object):
    GROUPID = None
    GROUP_VCS='gnomecvs'

    FTPROOT='/ftp/pub/GNOME'
    FTPROOT_DEBUG='/ftp/tmp'
    URLROOT='https://download.gnome.org'
    BLOCKSIZE=2*1024*1024 # (dot will be printed per block for progress indication)

    # Note: this defines the formats install-module can read
    #       formats install-module creates are defined in
    #       ModuleInstall.INSTALL_FORMATS
    #
    # WARNING: When extending this, make sure tarfile.TarFile
    #          actually also supports the new compression!
    #          See e.g. XzTarFile class
    FORMATS = {
        'tar.gz': gzip.GzipFile,
        'tar.bz2': bz2.BZ2File,
        'tar.xz': lzma.LZMAFile
    }

    DIFF_FILES = [
        # Filename in tarball; extension on ftp.gnome.org; heading name
        ('NEWS', 'news', 'News'),
        ('ChangeLog', 'changes', 'ChangeLog')
    ]
    DIFF_FILES_DICT = dict([(a,(b,c)) for a,b,c in DIFF_FILES])

class DOAP(BasicInfo):
    JSONVERSION = 1

    NS_DOAP = "http://usefulinc.com/ns/doap#"
    #NS_FOAF = "http://xmlns.com/foaf/0.1/"
    NS_GNOME = "http://api.gnome.org/doap-extensions#"

    DOAP_URL = 'https://gitlab.gnome.org/repositories.doap'
    DOAP_CACHE = '/ftp/cache/doap.json'
    GITLAB_REPO = 'ssh://git@gitlab.gnome.org'

    TARBALL_PATH_PREFIX = '/sources/'
    TARBALL_HOSTNAME_SUFFIX = '.gnome.org'

    PROPERTIES = ('description', 'shortdesc', 'name')
    PROPERTIES_AS_LIST = ('bug-database', )


    # http://www.artima.com/forums/flat.jsp?forum=122&thread=15024

    def __init__(self):
        self.jsonfile = self.DOAP_CACHE
        self._init_doap()

    def get_module(self, tarball):
        modules = self.tarball_to_module.get(tarball, [])
        if not modules: modules.append(tarball)

        if len(modules) == 1:
            return list(modules)[0]
        elif tarball in modules:
            return tarball
        else:
            return sorted(modules, key=len)[0]

    def _init_doap(self, force_refresh=False):

        # Get module maintainer data from DOAP file in Git
        # Note: some data is still in MAINTAINERS files. These are converted
        #       to DOAP information by scripts in gitadmin-bin module.

        changed = False
        etag = None
        last_modified = None

        # XXX - unfinished
        if not os.path.exists(self.jsonfile):
            force_refresh = True

        if not force_refresh:
            j = json.load(open(self.jsonfile, 'rb'))
            json_ver = j[0]
            if json_ver == self.JSONVERSION:
                json_ver, etag, last_modified, info, TARBALL_TO_MODULE, UID_TO_MODULES = j
                if not len(info):
                    force_refresh=True
            elif json_ver > self.JSONVERSION:
                print >>sys.stderr, "ERROR: Json newer than supported version, ignoring json"
                force_refresh=True
            else:
                force_refresh=True

        req = urllib2.Request(self.DOAP_URL)

        if not force_refresh:
            if etag:
                    req.add_header("If-None-Match", etag)
            if last_modified:
                    req.add_header("If-Modified-Since", last_modified)

        try:
            # Always need to check if there's any newer information
            url_handle = urllib2.urlopen(req)
        except urllib2.HTTPError, e:
            if e.code == 304:
                pass
            elif force_refresh:
                print >>sys.stderr, "ERROR: Cannot read DOAP file and no old copy available"
            else:
                print e.code
                print >>sys.stderr, "WARNING: Cannot retrieve DOAP file; using old copy"
        else:
            etag, last_modified, info, TARBALL_TO_MODULE, UID_TO_MODULES = self._parse_url_handle(url_handle)
            changed = True

        self.etag = etag
        self.last_modified = last_modified
        self.info = info
        self.tarball_to_module = TARBALL_TO_MODULE
        self.uid_to_module = UID_TO_MODULES

        if changed:
            # save the new information
            self.write_json()

    def _parse_url_handle(self, url_handle):
        UID_TO_MODULES = {}
        TARBALL_TO_MODULE = {}
        MODULE_INFO = {}

        TARBALL_PATH_PREFIX_LEN = len(self.TARBALL_PATH_PREFIX)

        headers = url_handle.info()
        etag = headers.getheader("ETag")
        last_modified = headers.getheader("Last-Modified")

        nodes = semi_rdf.read_rdf(url_handle)
        for node in nodes:
            if node.name != (self.NS_DOAP, "Project"):
                continue

            repo = node.find_property((self.NS_DOAP, u'repository'))
            modname = None
            if isinstance(repo, semi_rdf.Node):
                repo_loc = repo.find_property((self.NS_DOAP, u'location'))

                if hasattr(repo_loc, 'startswith'):
                    modname = re.sub('%s:(GNOME|Infrastructure)/' % self.GITLAB_REPO, '', repo_loc)
                    modname = modname.split('.')[0]

            # In case project is unknown or already defined, ignore it
            if not modname or modname in MODULE_INFO:
                continue

            MODULE_INFO[modname] = {}

            tarballs = [url.path[url.path.index(self.TARBALL_PATH_PREFIX) + TARBALL_PATH_PREFIX_LEN:].split('/')[0] for url in [urlparse.urlparse(url) for url in node.find_properties((self.NS_DOAP, u'download-page')) if isinstance(url, semi_rdf.UrlResource)] if self.TARBALL_PATH_PREFIX in url.path and url.hostname.endswith(self.TARBALL_HOSTNAME_SUFFIX)]

            if tarballs:
                MODULE_INFO[modname]['tarballs'] = set(tarballs)

                for tarball in tarballs:
                    TARBALL_TO_MODULE.setdefault(tarball, set()).add(modname)

            maints = set()
            for maint in node.find_properties((self.NS_DOAP, u'maintainer')):
                if not isinstance(maint, semi_rdf.Node):
                    continue

                uid = maint.find_property((self.NS_GNOME, u'userid'))
                if not isinstance(uid, basestring):
                    continue

                uid = str(uid)

                maints.add(uid)

                UID_TO_MODULES.setdefault(uid, set()).add(modname)

            if maints:
                MODULE_INFO[modname]['maintainers'] = maints

            for prop in self.PROPERTIES:
                val = node.find_property((self.NS_DOAP, prop))
                if val is not None:  MODULE_INFO[modname][prop] = val

            for prop in self.PROPERTIES_AS_LIST:
                val = node.find_properties((self.NS_DOAP, prop))
                if val: MODULE_INFO[modname][prop] = list(val)

        return (etag, last_modified, MODULE_INFO, TARBALL_TO_MODULE, UID_TO_MODULES)

    def write_json(self):
        # Want to overwrite any existing file and change the owner
        if os.path.exists(self.jsonfile):
            os.remove(self.jsonfile)
        with open(self.jsonfile, 'w') as f:
            json.dump((self.JSONVERSION, self.etag, self.last_modified, self.info, self.tarball_to_module, self.uid_to_module), f, cls=SetEncoder)
            if self.GROUPID is not None:
                os.fchown(f.fileno(), -1, self.GROUPID)


class TarInfo(BasicInfo):

    def __init__(self, path, files=set()):
        self.path = path
        self.file = {}

        self.dirname, self.basename = os.path.split(path)

        tarinfo_files = files.copy()

        r = re_file.match(self.basename)
        if r:
            fileinfo = r.groupdict()

            self.module = fileinfo['module']
            self.version = fileinfo['version']
            self.format = fileinfo['format']
            self.majmin = re_majmin.sub(r'\1', fileinfo['version'])

            for tarballname, format, formatname in self.DIFF_FILES:
                tarinfo_files.add('%s-%s/%s' % (self.module, self.version, tarballname))
        else:
            self.module = None
            self.version = None
            self.format = None
            self.majmin = None

        self.files = tarinfo_files

    def check(self, progress=False):
        """Check tarball consistency"""
        if hasattr(self, '_errors'):
            return self._errors

        errors = {}
        files = self.files

        t = None
        try:
            # This automatically determines the compression method
            # However, it does that by just trying to open it with every compression method it knows
            # and seeing what succeeds. Which is somewhat inefficient
            t = tarfile.open(self.path, 'r')

            size_files = 0
            file_count = 0
            uniq_dir = None
            dots_shown = 0
            for info in t:
                file_count += 1
                size_files += info.size

                if info.name in files:
                    self.file[os.path.basename(info.name)] = t.extractfile(info).readlines()

                if file_count == 1:
                    if '/' in info.name.lstrip('/'):
                        uniq_dir = "%s/" % info.name.lstrip('/').partition('/')[0]
                    elif info.isdir():
                        uniq_dir = "%s/" % info.name
                elif uniq_dir is not None and not info.name.startswith(uniq_dir) and \
                     not ( info.isdir() and uniq_dir == '%s/' % info.name ):
                    uniq_dir = None
                if progress:
                    dots_to_show = t.offset / self.BLOCKSIZE
                    if dots_to_show > dots_shown:
                        sys.stdout.write("." * (dots_to_show - dots_shown))
                        dots_shown = dots_to_show

            # Now determine the current position in the tar file
            tar_end_of_data_pos = t.fileobj.tell()
            # as well as the last position in the tar file
            # Note: doing a read as seeking is often not supported :-(
            while t.fileobj.read(self.BLOCKSIZE) != '':
                if progress:
                    sys.stdout.write(".")
            tar_end_of_file_pos = t.fileobj.tell()


            test_uniq_dir = '%s-%s/' % (self.module, self.version)
            if uniq_dir is None:
                errors['NO_UNIQ_DIR'] = 'Files should all be in one directory (%s)' % test_uniq_dir
            elif uniq_dir != test_uniq_dir:
                errors['UNIQ_DIR'] = 'Files not in the correct directory (expected %s, found %s)' % (test_uniq_dir, uniq_dir)

            test_eof_data = (tar_end_of_file_pos - tar_end_of_data_pos)
            # MAX_EXTRA_DATA=20480
            # if test_eof_data > MAX_EXTRA_DATA:
            #     errors['EXTRA_DATA'] = 'Too much uncompressed tarball data (expected max %s, found %s); use tar-ustar in AM_INIT_AUTOMAKE!' % (human_size(MAX_EXTRA_DATA), human_size(test_eof_data))

            if not isinstance(t.fileobj, self.FORMATS.get(self.format, "")):
                errors['WRONG_EXT'] = 'Compression used is different than what extension suggests'

            self.size_files = size_files
            self.file_count = file_count
            self.tar_end_of_data_pos = tar_end_of_data_pos
            self.tar_end_of_file_pos = tar_end_of_file_pos
            self.uniq_dir = uniq_dir
        except tarfile.ReadError:
            errors['INVALID_FILE'] = 'Tarball cannot be read'
        finally:
            if t:
                t.close()

        self._errors = errors
        return self._errors

    def diff(self, files, prev_tarinfo, constructor, progress=False):
        diffs = {}
        prev_errors = False

        # Only diff if the current tarbal has at least one file to diff
        found_files = len([fn for fn in files if fn in self.file])
        if not found_files:
            return diffs

        if prev_tarinfo:
            if progress:
                sys.stdout.write(" - Checking previous tarball: ")
            prev_errors = prev_tarinfo.check(progress)
            if not prev_errors:
                if progress:
                    print ", done"
            else:
                if progress:
                    print ", failed (ignoring previous tarball!)"

        for fn in files:
            if fn not in self.file:
                continue

            if progress:
                sys.stdout.write(" - %s" % fn)

            f = constructor(fn)
            if prev_tarinfo is not None and fn in prev_tarinfo.file:
                context = 0
                a = prev_tarinfo.file[fn]
                b = self.file[fn]
                break_for = False
                lines = 0
                for group in difflib.SequenceMatcher(None,a,b).get_grouped_opcodes(context):
                    i1, i2, j1, j2 = group[0][1], group[-1][2], group[0][3], group[-1][4]
                    for tag, i1, i2, j1, j2 in group:
                        if tag == 'replace' or tag == 'insert':
                            lines += j2 - j1
                            f.writelines(b[j1:j2])
                            break_for = True
                    if break_for:
                        break
                if lines > 2:
                    f.flush()
                    diffs[fn] = f
                    if progress:
                        print ", done (diff, %s lines)" % lines
                else:
                    if progress:
                        print ", ignored (no change)"
                    if hasattr(f, 'name'):
                        os.remove(f.name)
            elif not prev_errors:
                # succesfully read previous tarball, didn't find a 'NEWS' / 'ChangeLog'
                # assume file has been added in this release and no diff is needed
                f.writelines(self.file[fn])
                f.flush()
                diffs[fn] = f
                print ", done (new file)"
            else:
                print ", ignored (previous tarball is not valid)"

        return diffs


class DirectoryInfo(BasicInfo):
    JSONVERSION = 4

    def __init__(self, relpath, limit_module=None):
        self.relpath = relpath
        self.module = limit_module
        self.jsonfile = os.path.join(self.FTPROOT, relpath, 'cache.json')

        self.read_json()

    def refresh(self):
        self.read_json(force_refresh=True)

    def read_json(self, force_refresh=False):
        info = {}
        ignored = {}
        changed = False

        if not os.path.exists(self.jsonfile):
            force_refresh = True

        if not force_refresh:
            j = json.load(open(self.jsonfile, 'rb'))
            json_ver = j[0]
            if json_ver == self.JSONVERSION:
                json_ver, info, json_versions, ignored = j
                if not len(info):
                    force_refresh=True
            elif json_ver > self.JSONVERSION:
                print >>sys.stderr, "ERROR: Json newer than supported version, ignoring json"
                force_refresh=True
            else:
                force_refresh=True

        absdir = os.path.join(self.FTPROOT, self.relpath)
        if force_refresh and os.path.exists(absdir):
            curdir = os.getcwd()
            try:
                # Ensures paths are relative to the moduledir
                os.chdir(absdir)
                for root, dirs, files in os.walk(".", topdown=False):
                    saneroot = root[2:] if root.startswith("./") else root
                    for filename in files:
                        r = re_file.match(filename)
                        if r:
                            changed = True

                            fileinfo = r.groupdict()
                            module = fileinfo['module']
                            version = fileinfo['version']
                            format = fileinfo['format']

                            if module not in info:
                                info[module] = {}

                            if version not in info[module]:
                                info[module][version] = {}

                            if self.module is None or module == self.module:
                                info[module][version][format] = os.path.join(saneroot, filename)
                                continue

                        # If we arrive here, it means we ignored the file for some reason
                        if saneroot not in ignored:
                            ignored[saneroot] = []
                        ignored[saneroot].append(filename)
            finally:
                os.chdir(curdir)

        # XXX - maybe remove versions which lack tar.*

        self._info = info
        versions = {}
        if self.module:
            versions[self.module] = []
        for module in info.keys():
            versions[module] = sorted(info[module], version_cmp)
        self._versions = versions
        self._ignored = ignored

        if changed:
            # save the new information
            self.write_json()

    def determine_file(self, module, version, format, fuzzy=True, relative=False):
        """Determine file using version and format

        If fuzzy is set, possibly return a compressed version of the given
        format."""
        if module not in self._info:
            return None

        if version not in self._info[module]:
            return None

        formats = [format]
        if fuzzy and not "." in format:
            formats.extend(("%s.%s" % (format, compression) for compression in ("gz", "bz2", "xz")))

        info_formats = self._info[module][version]
        for f in formats:
            if f in info_formats:
                return os.path.join(self.relpath, info_formats[f]) if relative else \
                        os.path.join(self.FTPROOT, self.relpath, info_formats[f])

        return None

    def info_detailed(self, module, version, format, fuzzy=False):
        """Provides detailed information about file references by
        version and format.

        If fuzzy is set, possibly return a compressed version of the given
        format."""
        relpath = DirectoryInfo.determine_file(self, module, version, format, fuzzy=fuzzy, relative=True)
        if relpath is None:
            return None

        realpath = os.path.join(self.FTPROOT, relpath)

        stat = os.stat(realpath)
        return (relpath, realpath, human_size(stat.st_size), stat)

    def write_json(self):
        # Want to overwrite any existing file and change the owner
        if os.path.exists(self.jsonfile):
            os.remove(self.jsonfile)
        with open(self.jsonfile, 'w') as f:
            json.dump((self.JSONVERSION, self._info, self._versions, self._ignored), f)
            if self.GROUPID is not None:
                os.fchown(f.fileno(), -1, self.GROUPID)

    @property
    def info(self):
        return self._info

    @property
    def versions(self):
        return self._versions

    @property
    def ignored(self):
        return self._ignored


class SuiteInfo(DirectoryInfo):

    def __init__(self, suite, version):
        majmin = re_majmin.sub(r'\1', version)
        relpath = os.path.join(suite, majmin, version)
        DirectoryInfo.__init__(self, relpath)

    def diff(self, oldversion, obj=sys.stdout):
        # XXX  -- assert self.suite == oldversion.suite
        import textwrap

        def moduleprint(modules, header):
            if modules:
                print >>obj, "%s:" % header
                print >>obj, textwrap.fill(", ".join(sorted(list(modules))), width=78,
                                    break_long_words=False, break_on_hyphens=False,
                                    initial_indent='   ', subsequent_indent='   ')
                print >>obj, ""


        oldmodules = set(oldversion.versions.keys())
        newmodules = set(self.versions.keys())
        modules = set()
        modules.update(oldmodules)
        modules.update(newmodules)

        addedmodules = newmodules - oldmodules
        removedmodules = oldmodules - newmodules
        samemodules = oldmodules & newmodules
        moduleprint(addedmodules, "The following modules have been added in this release")
        moduleprint(removedmodules, "The following modules have been removed in this release")

        news = {}
        sameversions = set()
        header = "The following modules have a new version"
        did_header = False
        have_no_news = False
        have_errors = False
        for module in sorted(samemodules):
            show_contents = True
            newmodulever = self.versions.get(module, (None,))[-1]
            new_file = self.determine_file(module, newmodulever, 'tar') if newmodulever else None

            prevmodulever = oldversion.versions.get(module, (None,))[-1]
            prev_file = oldversion.determine_file(module, prevmodulever, 'tar') if prevmodulever else None

            if not new_file:
                continue

            if newmodulever == prevmodulever:
                sameversions.add(module)
                continue

            if not did_header:
                print >>obj, "%s:" % header
                did_header=True
            obj.write(" - %s (%s => %s)" % (module, prevmodulever or '-none-', newmodulever or '-none'))


            fn = 'NEWS'

            new_tarinfo = TarInfo(new_file)
            new_errors = new_tarinfo.check()
            if new_errors:
                have_errors=True
                print >>obj, " (E)"
                continue

            prev_tarinfo = TarInfo(prev_file) if prev_file else None

            constructor = lambda fn: StringIO()
            diffs = new_tarinfo.diff((fn, ), prev_tarinfo, constructor, progress=False)

            if fn in diffs:
                news[module] = diffs[fn]
                news[module].seek(0)
            else:
                have_no_news=True
                obj.write(" (*)")

            print >>obj, ""
        if did_header:
            if have_no_news:
                print >>obj, "(*) No summarized news available"
            if have_errors:
                print >>obj, "(E) No summarized news available due to tarball validation error"
            print >>obj, ""

        moduleprint(sameversions, "The following modules weren't upgraded in this release")

        for module in sorted(news):
            print >>obj, "========================================"
            print >>obj, "  %s" % module
            print >>obj, "========================================"
            print >>obj, ""
            print >>obj, news[module].read()


class ModuleInfo(DirectoryInfo):

    def __init__(self, module, section=DEFAULT_SECTION):
        self.module = module
        self.section = section

        relpath = os.path.join(self.section, self.module)
        DirectoryInfo.__init__(self, relpath, limit_module=module)

    def _set_doap(self):
        # Determine maintainers and module name

        # single instance
        doap = DOAP()
        self.__class__._doap = doap

        # get_from_doap relies on self._reponame being set
        self._reponame = doap.get_module(self.module)

        # Limit maintainers to anyone being a member of GROUP_VCS
        maints = set(self.get_from_doap('maintainers', []))
        if maints:
            try:
                maints = set(grp.getgrnam(self.GROUP_VCS).gr_mem).intersection(maints)
            except KeyError:
                maints = set()

        self._maintainers = maints

    @property
    def maintainers(self):
        if not hasattr(self, '_maintainers'):
            self._set_doap()

        return self._maintainers

    @property
    def reponame(self):
        if not hasattr(self.__class__, '_doap'):
            self._set_doap()

        return self._reponame

    @property
    def doap(self):
        if not hasattr(self.__class__, '_doap'):
            self._set_doap()

        return self.__class__._doap

    def get_from_doap(self, needle, default=None):
        return self.doap.info.get(self._reponame, {}).get(needle, default)

    def get_bz_product_from_doap(self):
        for bz in self.get_from_doap('bug-database', []):
            url = urlparse.urlparse(bz)
            if url.netloc == 'bugzilla.gnome.org':
                d = urlparse.parse_qs(url.query)
                if 'product' in d:
                    yield d['product'][0]

    @property
    def versions(self):
        return self._versions[self.module]

    def determine_file(self, version, format, fuzzy=True, relative=False):
        return DirectoryInfo.determine_file(self, self.module, version, format, fuzzy, relative)

    def info_detailed(self, version, format, fuzzy=False):
        return DirectoryInfo.info_detailed(self, self.module, version, format, fuzzy=False)


class InstallModule(BasicInfo):

    # Preferred format should appear last
    INSTALL_FORMATS = ('tar.xz',)

    def __init__(self, file, section=DEFAULT_SECTION):
        self.file = file

        self.uid = os.getuid()
        self.pw = pwd.getpwuid(self.uid)
        self.who = self.pw.pw_gecos
        self.who = re_who.sub("", self.who)
        if self.who == "":
            self.who = self.pw.pw_name

        self.section = section
        self.dirname, self.basename = os.path.split(file)
        self.fileinfo = TarInfo(file)

        if self.fileinfo.module is not None:
            self.module = self.fileinfo.module
            self.majmin = self.fileinfo.majmin
            self.version = self.fileinfo.version
            self.format = self.fileinfo.format

            self.destination = os.path.join(self.FTPROOT, self.section, self.fileinfo.module, self.majmin)
            if DEBUG:
                self.destination = os.path.join(self.FTPROOT_DEBUG, self.section, self.fileinfo.module, self.majmin)
        else:
            self._moduleinfo = None
            self.module = None

    @property
    def moduleinfo(self):
        if not hasattr(self, '_moduleinfo'):
            self._moduleinfo = ModuleInfo(self.fileinfo.module, section=self.section)

        return self._moduleinfo

    @property
    def prevversion(self):
        if not hasattr(self, '_prevversion'):
            self._prevversion = get_latest_version(self.moduleinfo.versions, self.version)

        return self._prevversion

    def confirm_install(self):

        print """
      Module: %s
     Version: %s   (previous version: %s)
 Destination: %s/""" % (self.module, self.version, self.prevversion or 'N/A', self.destination)

        # Check if the module directory already exists. If not, the module name might contain a typo
        if not os.path.isdir(os.path.join(self.FTPROOT, self.section, self.module)):
            print """
WARNING: %s is not present in the archive!
         Are you sure that it is new and/or the correct module name?""" % self.module

        print """
Install %s? [Y/n]""" % self.module,
        response = raw_input()

        if response != '' and response[0] != 'y' and response[0] != 'Y':
            print """Module installation cancelled."""

            return False

        # install the module
        return True

    def validate(self, clobber=False):
        if self.module is None:
            print >>sys.stderr, 'ERROR: Unrecognized module/version/file format. Make sure to follow a sane naming scheme (MAJOR.MINOR.MICRO)'
            return False

        if self.format not in self.FORMATS:
            print >>sys.stderr, 'ERROR: Unrecognized file format \'.%s\'' % self.format
            return False

        # Don't allow an existing tarball to be overwritten
        if not DEBUG:
            if not clobber and self.version in self.moduleinfo.versions:
                print >>sys.stderr, """ERROR: %s already exists in the archive!""" % self.basename
                return False
        else:
            # When debugging, only check for the exact tarball name
            if os.path.exists(os.path.join(self.destination, self.basename)):
                print >>sys.stderr, """ERROR: %s already exists in the archive!""" % self.basename
                return False

        # XXX - verify if tarball is being installed by a maintainer

        # CHECK FOR CONSISTENCY
        sys.stdout.write(" - Checking consistency: ")
        errors = self.fileinfo.check(progress=True)
        if not errors:
            print ", done"
        else:
            print ", failed"
            for k, v in errors.iteritems():
                print >>sys.stderr, "ERROR: %s" % v

        # True if there are no errors
        return len(errors) == 0

    def install(self, unattended=False, clobber=False):
        print "Preparing installation of %s:" % self.basename
        # Validate the file
        if not self.validate(clobber):
            return False


        tmpdir = tempfile.mkdtemp(prefix='install_module')
        try:
            created_files = []
            # do we have a previous version?
            prev_file = self.moduleinfo.determine_file(self.prevversion, 'tar') if self.prevversion else None
            prev_tarinfo = TarInfo(prev_file) if prev_file else None

            constructor = lambda fn: self._make_tmp_file(tmpdir, self.DIFF_FILES_DICT[fn][0])
            diffs = self.fileinfo.diff(self.DIFF_FILES_DICT, prev_tarinfo, constructor, progress=True)

            for fn, f in diffs.iteritems():
                created_files.append(f.name)

            # Create tarball(s) according to INSTALL_FORMATS
            if self.format in self.INSTALL_FORMATS:
                sys.stdout.write(" - Copying %s" % self.format)
                with open(self.file, 'rb') as f1:
                    with self._make_tmp_file(tmpdir, self.format) as f2:
                        created_files.append(f2.name)
                        shutil.copyfileobj(f1, f2)
                print ", done"

            formats = [format for format in self.INSTALL_FORMATS if format != self.format]
            if len(formats):
                if len(formats) == 1:
                    sys.stdout.write(" - Creating %s from %s: " % (formats[0], self.format))
                else:
                    sys.stdout.write(" - Creating tarballs from %s: " % self.format)
                f2 = []
                for format in formats:
                    if len(formats) > 1:
                        sys.stdout.write("%s " % format)
                    f = self._make_tmp_file(tmpdir, format, constructor=self.FORMATS[format])
                    created_files.append(f.name)
                    f2.append(f)

                f1 = self.FORMATS[self.format](self.file, 'rb')
                while 1:
                    buf = f1.read(self.BLOCKSIZE)
                    if not buf:
                        break
                    for fdst in f2:
                        fdst.write(buf)
                        sys.stdout.write(".")
                for fdst in f2:
                    fdst.close()
                    f2 = []
                print ", done"



            sys.stdout.write(" - Creating sha256sum")
            with self._make_tmp_file(tmpdir, 'sha256sum') as f:
                cmd = ['sha256sum', '--']
                cmd.extend([os.path.basename(fn) for fn in created_files if os.path.isfile(fn)])
                subprocess.call(cmd, stdout=f, cwd=tmpdir)
                created_files.append(f.name)
            print ", done"

            # Ask user if tarball should be installed
            if not unattended:
                if not self.confirm_install():
                    return False

            print "Installing %s:" % self.basename

            if not os.path.isdir(self.destination):
                sys.stdout.write(' - Creating directory')
                makedirs_chown(self.destination, 042775, -1, self.GROUPID or -1) # drwxrwsr-x
                print ", done"
            sys.stdout.write(' - Moving files: ')
            for fn in created_files:
                dest = os.path.join(self.destination, os.path.basename(fn))
                shutil.move(fn, dest)
                if self.GROUPID is not None:
                    os.chown(dest, -1, self.GROUPID)
                sys.stdout.write('.')
            print ", done"

            sys.stdout.write(' - Updating LATEST-IS')
            for extension in reversed(self.INSTALL_FORMATS + ('tar.gz',)):
                latest = '%s-%s.%s' % (self.module, self.version, extension)
                if os.path.exists(os.path.join(self.destination, latest)):
                    for fn in glob.glob(os.path.join(self.destination, 'LATEST-IS-*')):
                        os.remove(fn)
                    os.symlink(latest, os.path.join(self.destination, 'LATEST-IS-%s' % self.version))
                    break
            print ", done"
        finally:
            # cleanup temporary directory
            shutil.rmtree(tmpdir)

        sys.stdout.write(" - Updating known versions")
        self.moduleinfo.refresh()
        print ", done"

        sys.stdout.write(" - Removing original tarball")
        if self.GROUPID is not None and os.stat(self.file).st_gid != self.GROUPID:
            os.remove(self.file)
            print ", done"
        else:
            print ", ignored (owned by protected group)"

        self.inform()
        return True

    def _make_tmp_file(self, tmpdir, format, constructor=open):
        fn = os.path.join(tmpdir, '%s-%s.%s' % (self.module, self.version, format))
        f = constructor(fn, 'w')
        if self.GROUPID is not None:
            os.chown(fn, -1, self.GROUPID)
        return f

    def _print_header(self, obj, header):
        print >>obj, header
        print >>obj, "=" * len(header)

    def inform(self):
        """Inform regarding the new release"""
        print "Doing notifications:"
        if self.version not in self.moduleinfo.versions:
            print "ERROR: Cannot find new version?!?"
            return False

        import textwrap

        sha256sum = {}
        sys.stdout.write(" - Informing ftp-release-list")

        mail = StringIO()

        realpath = self.moduleinfo.determine_file(self.version, 'sha256sum', fuzzy=False)
        if realpath is not None:
            with open(realpath, "r") as f:
                for line in line_input(f):
                    # XXX - the checksum filed could look differently (binary indicator)
                    if '  ' in line:
                        checksum, file = line.partition('  ')[::2]
                        sha256sum[file] = checksum
                    else:
                        print "WARN: Strange sha256sum line: %s" % line
        else:
            print "WARN: Couldn't determine sha256sum file?!?"

        headers = {
            'Reply-To': 'desktop-devel-list@gnome.org',
            'X-Module-Name': self.module,
            'X-Module-Version': self.version,
            'X-Maintainer-Upload': str(self.pw.pw_name in self.moduleinfo.maintainers)
        }

        modulename = None
        desc = self.moduleinfo.get_from_doap('description')
        desc = self.moduleinfo.get_from_doap('shortdesc') if desc is None else desc
        if desc is not None:
            modulename = self.moduleinfo.get_from_doap('name', self.module)
            self._print_header(mail, "About %s" % (modulename or self.module))
            print >>mail, ""
            for paragraph in desc.encode('utf-8').split("\n\n"):
                if "\n" in paragraph: paragraph = re_whitespace.sub(" ", paragraph)
                print >>mail, textwrap.fill(paragraph)
                print >>mail, ""

        show_contents = True
        for tarballname, format, formatname in self.DIFF_FILES:
            info = self.moduleinfo.info_detailed(self.version, format)
            if info is not None:
                path, realpath, size, stat = info
                if show_contents and stat.st_size < 50000:
                    with open(realpath, 'r') as f:
                        do_version = True
                        stripchars = "".join((string.punctuation, string.whitespace))
                        line = f.readline()
                        while line != '' and (line.strip(stripchars) == '' \
                                              or (do_version and self.version in line)):
                            if self.version in line:
                                do_version = False
                            line = f.readline()

                        if line == '':
                            # No interesting line in this file, ignore it
                            continue

                        self._print_header(mail, formatname)
                        print >>mail, ""
                        mail.write(line)
                        shutil.copyfileobj(f, mail)
                else:
                    self._print_header(mail, formatname)
                    mail.write("%s/%s  (%s)" % (self.URLROOT, path, size))
                headers['X-Module-URL-%s' % format] = "%s/%s" % (self.URLROOT, path)
                print >>mail, ""
                # Only show the contents of the first found file, URLs for the rest
                show_contents = False

        print >>mail, ""
        self._print_header(mail, 'Download')
        infos = [(format, self.moduleinfo.info_detailed(self.version, format)) for format in self.FORMATS]
        infos = [(format,) + info for format, info in infos if info is not None]
        max_format_len = max((len(info[0]) for info in infos))
        if len(infos) > 1:
            print >>mail, ""
        for format, path, realpath, size, stat in infos:
            dirname, basename = os.path.split(path)
            print >>mail, "%s/%s %s(%s)" % (self.URLROOT, path, ' ' * (max_format_len - len(format)),  size)
            if basename in sha256sum:
                print >>mail, "  sha256sum: %s" % sha256sum[basename]
                headers['X-Module-SHA256-%s' % format] = sha256sum[basename]
            headers['X-Module-URL-%s' % format] = "%s/%s" % (self.URLROOT, path)
            print >>mail, ""


        mail.seek(0)
        subject = '%s %s' % (self.module, self.version)
        to = "FTP Releases <ftp-release-list@gnome.org>"
        smtp_to = ['%s@src.gnome.org' % maint for maint in self.moduleinfo.maintainers]
        if not smtp_to:
            smtp_to = ['release-team@gnome.org']
        smtp_to.append('ftp-release-list@gnome.org')
        retcode = self._send_email(mail.read(), subject, to, smtp_to, headers)
        print ", done"

        sys.stdout.write(" - Triggering GNOME library update")
        subject = 'GNOME_GIT library-web'
        to = "gnomeweb@webapps.gnome.org"
        retcode = self._send_email("forced", subject, to, [to])
        print ", done"

        sys.stdout.write(" - Triggering ftp.gnome.org update")
        cmd = ['/usr/local/bin/signal-ftp-sync']
        if self._call_cmd(cmd):
            print """
Your tarball will appear in the following location on ftp.gnome.org:

  %s

It is important to retain the trailing slash for compatibility with
broken http clients.""" % "/".join((self.URLROOT, self.section, self.module, self.majmin, ""))
            realpath = self.moduleinfo.determine_file(self.version, 'sha256sum', fuzzy=False)
            if realpath is not None:
                print ""
                with open(realpath, "r") as f:
                    shutil.copyfileobj(f, sys.stdout)

        print """
The ftp-release-list email uses information from the modules DOAP file. Make
sure at least the following fields are filled in:
  name, shortdesc, description, download-page, bug-database
See https://wiki.gnome.org/MaintainersCorner#doap"""


    def _call_cmd(self, cmd):
        """Calls a certain command and shows progress

        Note: returns True even if exit code is not zero."""

        if not os.path.isfile(cmd[0]):
            print ", FAILED (cannot find %s)" % cmd[0]
            print "PLEASE INFORM gnome-sysadmin@gnome.org ASAP!!!"

            return False

        if DEBUG:
            print ", ignored (debug mode)"
            return True

        retcode = subprocess.call(cmd)
        if retcode == 0:
            print ", done"
        else:
            print "FAILED (exit code %s)" % retcode

        return True


    def _send_email(self, contents, subject, to, smtp_to, headers=None):
        """Send an email"""
        msg = MIMEText(contents, _charset='utf-8')
        msg['Subject'] = subject
        msg['From'] = formataddr((Header(self.who.decode('utf-8')).encode(), 'install-module@master.gnome.org'))
        msg['To'] = to
        if headers is not None:
            for k, v in headers.iteritems():
                msg[k] = v

        if DEBUG:
            smtp_to = ['olav@vitters.nl']

        # Call sendmail program directly so it doesn't matter if the service is running
        cmd = ['/usr/sbin/sendmail', '-oi', '-f', 'noreply@gnome.org', '--']
        cmd.extend(smtp_to)
        p = subprocess.Popen(cmd, stdin=subprocess.PIPE)
        p.stdin.write(msg.as_string())
        p.stdin.flush()
        p.stdin.close()
        return p.wait()


class InstallSuites(BasicInfo):

    INSTALL_FORMATS = ('tar.gz', 'tar.bz2')

    def __init__(self, file, gnomever):
        self.file = file

        self.suites = {}
        self.moduleinfo = {}
        self.version = gnomever

        self.dirname, self.basename = os.path.split(file)

    def validate(self):
        print "Preparing installation of %s:" % self.basename
        is_valid = True
        suitedata = {}
        moduleversions = {}
        modulesuites = {}
        with open(self.file, 'r') as f:
            for line in line_input(f):
                if line == '' or line.startswith('#'):
                    continue
                data = line.split(':')
                if len(data) <> 4:
                    print 'ERROR: Bad line in datafile: %s' % line
                    is_valid = False
                    continue

                suite, module, version, subdir = data
                if suite not in suitedata:
                    suitedata[suite] = {}
                if module not in suitedata[suite]:
                    suitedata[suite][module] = []

                suitedata[suite][module].append((version, subdir))

                # For validation purposes:
                if module not in moduleversions:
                    moduleversions[module] = []
                moduleversions[module].append(version)

                if module not in modulesuites:
                    modulesuites[module] = set()
                modulesuites[module].add(suite)

        # Validate the suite
        for suite in suitedata:
            if suite not in SUITES:
                print 'ERROR: Invalid suite: %s' % suite
                is_valid = False

            majmin = re_majmin.sub(r'\1', self.version)
            abspath = os.path.join(self.FTPROOT, suite, majmin, self.version)
            if os.path.exists(abspath):
                print "ERROR: Suite already exists: %s " % abspath
                is_valid = False

        # Validate if the given module versions can be found
        for module, versions in moduleversions.iteritems():
            self.moduleinfo[module] = ModuleInfo(module)
            for version in versions:
                if version not in self.moduleinfo[module].versions:
                    print 'ERROR: Module %s doesn\'t have version %s' % (module, version)
                    is_valid = False
            # Module could have multiple versions, but that's pretty strange
            if len(versions) > 1:
                print 'WARNING: Module %s has multiple versions: %s' % (module, ", ".join(versions))

        # Validate if module is not in multiple suites
        for module, suites in modulesuites.iteritems():
            if len(suites) > 1:
                print 'ERROR: Module %s appears in multiple suites: %s' % (module, ", ".join(suites))
                is_valid = False

        if is_valid:
            self.suites = suitedata

        return is_valid

    def install(self, unattended=False):
        # Validate the file
        if not self.validate():
            return False

        print "Installating new suites:"
        suites = self.suites

        for suite in sorted(suites):
            sha256 = {}
            sys.stdout.write(" - Linking %s tarballs: " % suite)
            majmin = re_majmin.sub(r'\1', self.version)
            relpath = os.path.join(suite, majmin, self.version, 'sources')

            for module in sorted(suites[suite]):
                data = suites[suite][module]
                data.sort(lambda a, b: version_cmp(a[0], b[0]) or cmp(a[1], b[1]))
                for version, subdir in data:
                    relpath2 = relpath if subdir == '' else os.path.join(relpath, subdir)
                    abspath = os.path.join(self.FTPROOT, relpath2)
                    if not os.path.exists(abspath):
                        makedirs_chown(abspath, 042775, -1, self.GROUPID or -1) # drwxrwsr-x

                    for format in self.FORMATS:
                        relfile = self.moduleinfo[module].determine_file(version, format, fuzzy=False, relative=True)

                        if relfile is None:
                            continue

                        ext = os.path.splitext(relfile)[1].lstrip('.')
                        basename = os.path.basename(relfile)
                        if ext not in sha256:
                            sha256[ext] = []

                        if subdir == '':
                            sha256[ext].append(basename)
                        else:
                            sha256[ext].append(os.path.join(subdir, basename))

                        relfile = os.path.sep.join((['..'] * len(relpath2.split(os.path.sep))) + [relfile])


                        sys.stdout.write(".")
                        os.symlink(relfile, os.path.join(abspath, basename))
            print ""

            if os.path.exists(os.path.join(self.FTPROOT, relpath)) and sha256:
                sys.stdout.write(" - Generating sha256sums: ")
                for ext, files in sha256.iteritems():
                    sys.stdout.write("%s " % ext)
                    cmd = ['sha256sum', '--']
                    cmd.extend(files)
                    with open(os.path.join(self.FTPROOT, relpath, 'SHA256SUMS-for-%s' % ext), 'w') as f:
                        subprocess.call(cmd, stdout=f, cwd=os.path.join(self.FTPROOT, relpath))
                print ""


def cmd_install(options, parser):
    tarballs = [file for file in options.tarball if os.path.exists(file)]

    if not len(tarballs):
        parser.print_help()
        sys.exit(2)

    sys.stdout.write("Gathering information and sorting on version: ")
    modules = []
    for tarball in tarballs:
        modules.append(InstallModule(tarball))
        sys.stdout.write(".")
    print ", done"
    modules.sort(cmp=lambda x,y:
                     x.module and y.module and (cmp(x.module, y.module)
                                                or version_cmp(x.version, y.version)))

    for module in modules:
        module.install(unattended=options.unattended, clobber=options.clobber)
        print ""

    print """Please report any problems to:
https://gitlab.gnome.org/Infrastructure/Infrastructure/issues"""

def cmd_notify(options, parser):
    tarballs = [file for file in options.tarball if os.path.exists(file)]

    if not len(tarballs):
        parser.print_help()
        sys.exit(2)

    sys.stdout.write("Gathering information and sorting on version: ")
    modules = []
    for tarball in tarballs:
        modules.append(InstallModule(tarball))
        sys.stdout.write(".")
    print ", done"
    modules.sort(cmp=lambda x,y:
                     x.module and y.module and (cmp(x.module, y.module)
                                                or version_cmp(x.version, y.version)))

    for module in modules:
        module.inform()
        print ""

def cmd_show_info(options, parser):
    import datetime

    if not options.module:
        options.module = [os.path.basename(path) for path in glob.glob(os.path.join(BasicInfo.FTPROOT, options.section, '*')) if os.path.isdir(path)]
    for module in options.module:
        moduleinfo = ModuleInfo(module, options.section)
        version = moduleinfo.versions[-1] if len(moduleinfo.versions) else ""
        changed = ""
        if version:
            info = moduleinfo.info_detailed(version, 'tar.gz')
            if info:
                path, realpath, size, stat = info
                changed = datetime.date.fromtimestamp(stat.st_ctime).isoformat()

        print "\t".join((module, version, changed, ", ".join(moduleinfo.maintainers)))

def cmd_check_latest_is(options, parser):

    if not options.module:
        options.module = sorted([os.path.basename(path) for path in glob.glob(os.path.join(BasicInfo.FTPROOT, options.section, '*')) if os.path.isdir(path)])
    for module in options.module:
        moduleinfo = ModuleInfo(module, options.section)
        latest_dirs = set()
        for dir, files in moduleinfo.ignored.iteritems():
            for name in files:
                if name.startswith('LATEST-IS-'):
                    latest_dirs.add(dir)
                    break
        majmins = {}
        for version in moduleinfo.versions:
            majmin = re_majmin.sub(r'\1', version)
            if majmin not in majmins:
                majmins[majmin] = []
            majmins[majmin].append(version)
        for majmin in sorted(majmins.keys(), version_cmp):
            max_version = get_latest_version(majmins[majmin])
            latest_is = 'LATEST-IS-%s' % max_version
            has_other_latest = "WRONG" if majmin in latest_dirs else ""
            if majmin not in moduleinfo.ignored or latest_is not in moduleinfo.ignored[majmin]:
                print "\t".join((module, majmin, latest_is, has_other_latest))


def cmd_sudo(options, parser):
    print >>sys.stderr, "ERROR: Not yet implemented!"
    print ""
    print os.environ['SSH_ORIGINAL_COMMAND']
    sys.exit(2)

def cmd_show_ignored(options, parser):
    if options.module == '*':
        modules = [os.path.basename(path) for path in glob.glob(os.path.join(BasicInfo.FTPROOT, options.section, '*')) if os.path.isdir(path)]
    else:
        modules = [options.module]
    for module in modules:
        moduleinfo = ModuleInfo(module, section=options.section)
        for dir, files in moduleinfo.ignored.iteritems():
            for f in files:
                print "/".join((module, dir, f))

def cmd_show_doap(options, parser):
    import textwrap
    print options.module
    moduleinfo = ModuleInfo(options.module)
    desc = moduleinfo.get_from_doap('description', '')
    for paragraph in desc.split("\n\n"):
        if "\n" in paragraph: paragraph = re_whitespace.sub(" ", paragraph)
        print textwrap.fill(paragraph)
        print ""
    bz = moduleinfo.get_bz_product_from_doap()
    if bz:
        print "Bugzilla: %s" % ", ".join(bz)
    maints = moduleinfo.maintainers
    if maints:
        print "Maintainers: %s" % ", ".join(sorted(maints))

def cmd_validate_tarballs(options, parser):
    print options.module, options.section
    moduleinfo = ModuleInfo(options.module, section=options.section)
    for version in moduleinfo.versions:
        print "Version: %s" % version
        for format in BasicInfo.FORMATS:
            realpath = moduleinfo.determine_file(version, format, fuzzy=False)
            if realpath is not None:
                tarinfo = TarInfo(realpath)
                sys.stdout.write(" - Checking %s: " % format)
                errors = tarinfo.check(progress=True)
                if errors:
                    print ", FAILED"
                    for k, v in errors.iteritems():
                        print "ERROR: %s" % v
                else:
                    print ", success"

def cmd_release_diff(options, parser, header=None):
    oldversion = SuiteInfo(options.suite, options.oldversion)
    newversion = SuiteInfo(options.suite, options.newversion)

    did_header = False

    modules = set()
    modules.update(oldversion.versions.keys())
    modules.update(newversion.versions.keys())
    for module in sorted(modules):
        oldmodulever = oldversion.versions.get(module, ('-none-',))[-1]
        newmodulever = newversion.versions.get(module, ('-none-',))[-1]

        if newmodulever == oldmodulever:
            newmodulever = '-same-'
        elif options.same:
            # Only show modules which are the same
            continue

        if not did_header and header:
            did_header = True
            print header
            print ""
        print "%-35s %-15s %s" % (module, oldmodulever, newmodulever)

    if did_header:
        print ""

def cmd_simple_diff(options, parser):
    for suite in SUITES:
        options.suite = suite

        cmd_release_diff(options, parser, header="== %s ==" % suite)

def cmd_release_news(options, parser, header=None):
    oldversion = SuiteInfo(options.suite, options.oldversion)
    newversion = SuiteInfo(options.suite, options.newversion)

    newversion.diff(oldversion, obj=sys.stdout)

def cmd_simple_news(options, parser):
    diffs = []
    do_diff = True
    for suite in SUITES:
        newversion = SuiteInfo(suite, options.newversion)
        if not os.path.exists(os.path.join(newversion.FTPROOT, newversion.relpath)):
            continue

        oldversion = SuiteInfo(suite, options.oldversion)
        if not os.path.exists(os.path.join(oldversion.FTPROOT, oldversion.relpath)):
            continue

        news = os.path.join(newversion.FTPROOT, newversion.relpath, 'NEWS')
        if os.path.exists(news):
            print 'ERROR: %s already exists for %s %s' % (news, suite, options.newversion)
            do_diff = False

        diffs.append((newversion, oldversion))

    if do_diff:
        print "Generating news file(s):"
        for newversion, oldversion in diffs:
            f = open(os.path.join(newversion.FTPROOT, newversion.relpath, 'NEWS'), 'w')
            if BasicInfo.GROUPID is not None:
                os.fchown(f.fileno(), -1, BasicInfo.GROUPID)
            sys.stdout.write(" - %s " % f.name)
            newversion.diff(oldversion, obj=f)
            if f.tell() == 0:
                os.remove(f.name)
                print "uninteresting, not saved"
            else:
                print "saved"
            f.close()

def cmd_release_suites(options, parser):
    installer = InstallSuites(options.datafile, options.newversion)
    installer.install()


def main():
    try:
        groupid = grp.getgrnam(GROUP)[2]
    except KeyError:
        print >>sys.stderr, 'FATAL: Group %s does NOT exist!' % GROUP
        print >>sys.stderr, 'FATAL: Please inform gnome-sysadmin@gnome.org!'
        if not DEBUG:
            sys.exit(1)
        groupid = None

    if groupid is None or (os.getgid() != groupid and groupid not in os.getgroups()):
        print 'FATAL: Script requires membership of the %s group' % GROUP
        if not DEBUG:
            sys.exit(1)
    else:
        BasicInfo.GROUPID = groupid

    description = """Install new tarball(s) to GNOME FTP master and make it available on the mirrors."""
    epilog="""Report bugs to https://bugzilla.gnome.org/enter_bug.cgi?product=sysadmin"""
    parser = argparse.ArgumentParser(description=description,epilog=epilog)

    # SUBPARSERS
    subparsers = parser.add_subparsers(title='subcommands')
    #   install
    subparser = subparsers.add_parser('install', help='install a module to %s' % BasicInfo.URLROOT)
    subparser.add_argument("-f", "--force", action="store_true", dest="clobber",
                           help="Overwrite the original tarball")
    subparser.add_argument("-u", "--unattended", action="store_true",
                           help="do not prompt for confirmation")
    subparser.add_argument('tarball', nargs='+', help='Tarball(s) to install')
    subparser.add_argument("-s", "--section", choices=SECTIONS,
                           help="Section to install the file to")
    subparser.set_defaults(
        func=cmd_install, clobber=False, unattended=False, section=DEFAULT_SECTION
    )
    #   notify
    subparser = subparsers.add_parser('notify', help='notify new release')
    subparser.add_argument('tarball', nargs='+', help='Tarball(s) to notify')
    subparser.add_argument("-s", "--section", choices=SECTIONS)
    subparser.set_defaults(func=cmd_notify, section=DEFAULT_SECTION)
    #   show-info
    subparser = subparsers.add_parser('show-info', help='show module information')
    subparser.add_argument("-s", "--section", choices=SECTIONS)
    subparser.add_argument('module', nargs='*', help='Module(s) to show info for')
    subparser.set_defaults(func=cmd_show_info, section=DEFAULT_SECTION)
    # check-latest-is
    subparser = subparsers.add_parser('check-latest-is', help='check and correct LATEST-IS files')
    subparser.add_argument("-s", "--section", choices=SECTIONS)
    subparser.add_argument('module', nargs='*', help='Module(s) to show info for')
    subparser.set_defaults(func=cmd_check_latest_is, section=DEFAULT_SECTION)
    #   sudo
    subparser = subparsers.add_parser('sudo', help='install tarballs uploaded using rsync')
    subparser.set_defaults(func=cmd_sudo)
    #   doap
    subparser = subparsers.add_parser('doap', help='show information from DOAP file')
    subparser.add_argument('module', help='Module to show DOAP for')
    subparser.set_defaults(func=cmd_show_doap)
    #   validate-tarballs
    subparser = subparsers.add_parser('validate-tarballs', help='validate all tarballs for a given module')
    subparser.add_argument("-s", "--section", choices=SECTIONS,
                           help="Section to install the file to")
    subparser.add_argument('module', help='Module to validate')
    subparser.set_defaults(func=cmd_validate_tarballs, section=DEFAULT_SECTION)
    #   show-ignored
    subparser = subparsers.add_parser('show-ignored', help='Show ignored files in a module')
    subparser.add_argument("-s", "--section", choices=SECTIONS,
                           help="Section")
    subparser.add_argument('module', help='Module to check')
    subparser.set_defaults(func=cmd_show_ignored, section=DEFAULT_SECTION)

    # release-diff
    subparser = subparsers.add_parser('release-diff', help='show differences between two GNOME suite versions')
    subparser.add_argument("-s", "--suite", choices=SUITES,
                           help='Suite to compare')
    subparser.add_argument("--same", action="store_true",
                           help='Only show modules which have not changed')
    subparser.add_argument('oldversion', metavar='OLDVERSION', help='Previous GNOME version')
    subparser.add_argument('newversion', metavar='NEWVERSION', help='New GNOME version')
    subparser.set_defaults(func=cmd_release_diff, suite=DEFAULT_SUITE)
    # simple-diff
    subparser = subparsers.add_parser('simple-diff', help='Show differences between two GNOME versions in all suites')
    subparser.add_argument("--same", action="store_true",
                           help='Only show modules which have not changed')
    subparser.add_argument('oldversion', metavar='OLDVERSION', help='Previous GNOME version')
    subparser.add_argument('newversion', metavar='NEWVERSION', help='New GNOME version')
    subparser.set_defaults(func=cmd_simple_diff)
    # release-news
    subparser = subparsers.add_parser('release-news', help='show news between two GNOME suite versions')
    subparser.add_argument("-s", "--suite", choices=SUITES,
                           help='Suite to compare')
    subparser.add_argument('oldversion', metavar='OLDVERSION', help='Previous GNOME version')
    subparser.add_argument('newversion', metavar='NEWVERSION', help='New GNOME version')
    subparser.set_defaults(func=cmd_release_news, suite=DEFAULT_SUITE)
    # simple-news
    subparser = subparsers.add_parser('simple-news', help='Create NEWS file between two GNOME versions')
    subparser.add_argument('oldversion', metavar='OLDVERSION', help='Previous GNOME version')
    subparser.add_argument('newversion', metavar='NEWVERSION', help='New GNOME version')
    subparser.set_defaults(func=cmd_simple_news)
    # release-suites
    subparser = subparsers.add_parser('release-suites', help='release a new GNOME version')
    subparser.add_argument('newversion', metavar='NEWVERSION', help='New GNOME version')
    subparser.add_argument('datafile', metavar='DATAFILE', help='file which describes which modules to include')
    subparser.set_defaults(func=cmd_release_suites)


    if len(sys.argv) == 1:
        parser.print_help()
        sys.exit(2)

    options = parser.parse_args()

    old_mask = os.umask(0002)

    if DEBUG:
        print "WARNING: Running in DEBUG MODE!"

    try:
        options.func(options, parser)
    except KeyboardInterrupt:
        print('Interrupted')
        sys.exit(1)
    except EOFError:
        print('EOF')
        sys.exit(1)
    except IOError, e:
        if e.errno != errno.EPIPE:
            raise
        sys.exit(0)



if __name__ == "__main__":
    main()
