#!/usr/bin/env python3

import xml.etree.ElementTree as ET
import sys
import re
import copy
import os
import argparse

NSD = { 'xml': 'http://www.w3.org/XML/1998/namespace' }
DEFAULT_PRIMARY_LANG = 'en-US'

FRAG_PUNCT_OUTER = r'\[\]*()<>/?!+&€₤$%#“”":;`*=|\\'
FRAG_PUNCT_INNER = r'.,'
RE_PUNCT = re.compile(r'([{punct_outer}])'.format(punct_outer=FRAG_PUNCT_OUTER))
RE_PUNCT_INNER = re.compile(r'([{punct_inner}])'.format(punct_inner=FRAG_PUNCT_INNER))
RE_PUNCT_ALL = re.compile(r'([{punct_inner}{punct_outer}])'.format(punct_inner=FRAG_PUNCT_INNER, punct_outer=FRAG_PUNCT_OUTER))
RE_NUMBERS = re.compile(r'\b[0-9]+(?:(?:\.[0-9]+)+|(?:,[0-9]+))?\b')
RE_PHONE = re.compile(r'\+(?:\s*(?:-\s*)?\001){3,}')
FRAG_URL_PATH_COMPONENT = r'[a-zA-Z0-9_.-]+'
FRAG_DOMAIN_NAME = r'(?:[a-zA-Z][a-zA-Z0-9-]*\.)+[a-z]{2,}'
FRAG_URL_FREEFORM = r'[/a-zA-Z0-9_.-]+'
FRAG_URL_QUERYPARAM = r'[a-zA-Z0-9_]+={}'.format(FRAG_URL_FREEFORM)
FRAG_NON_TEXT = r'(?:\001|\002|[{punct_inner}{punct_outer}]+)'.format(punct_inner=FRAG_PUNCT_INNER, punct_outer=FRAG_PUNCT_OUTER)
RE_URL_OR_EMAIL = re.compile(r'\b(?:(http)s?://{dn}(?:/(?:(?:{pathcomp}/)*{pathcomp})?(?:\?{queryparam}(?:\&{queryparam})*)?(?:#{freeform})?)?|(www)\.{dn}\b|{dn}@{dn}\b)'.format(
    dn=FRAG_DOMAIN_NAME, pathcomp=FRAG_URL_PATH_COMPONENT, queryparam=FRAG_URL_QUERYPARAM, freeform=FRAG_URL_FREEFORM))
RE_LEAD_PUNCT = re.compile(r'^\s*(?:{non_text}\s+)*'.format(non_text=FRAG_NON_TEXT))
RE_TRAIL_PUNCT = re.compile(r'(?:\s+{non_text})*\s*$'.format(non_text=FRAG_NON_TEXT))
RE_ALL_PUNCT = re.compile(r'^\s*{non_text}\s*$'.format(non_text=FRAG_NON_TEXT))

PRIORITIES = {
    'ApprovedSignOff': 40,
    'ApprovedTranslation': 30,
    'Translated': 20,
    'Draft': 10,
}

class GlobalOpts:
    debug = False
    primary_lang = DEFAULT_PRIMARY_LANG
    report = False
    verbose = False

    def __init__(self, args=None):
        if args:
            if args.debug:
                self.debug = True

            if args.lang:
                self.primary_lang = args.lang

            if args.report:
                self.report = True

            if args.verbose:
                self.verbose = True



class MessageWriter:
    def __init__(self, opts=GlobalOpts()):
        self.verbose = opts.verbose

    def print(self, msg):
        print(msg, file=sys.stderr)

    def print_verbose(self, msg):
        if self.verbose:
            print(msg, file=sys.stderr)


def mangle_text_inner(s):
    """
    Helper: text fragment mangler

    Does text fragment conversions involving only simple regexp replacements:
    * Replace numbers and phones
    * Surround punctuation with spaces
    * Remove trailing and leading numbers and punctuation
    """
    # strip whitespace and lowercase
    s = s.strip().lower()

    # separate punctuation from words by whitespace
    s = RE_PUNCT.sub(r' \1 ', s)

    # replace numbers (including versions) with placeholders
    s = RE_NUMBERS.sub(' \001 ', s)

    # separate punctuation left from numeric replacement from words by whitespace
    s = RE_PUNCT_INNER.sub(r' \1 ', s)

    # postprocess: recognize phones
    s = RE_PHONE.sub(' \002 ', s)

    # postprocess: remove leading/trailing numbers and punctuation
    s = RE_LEAD_PUNCT.sub('', RE_TRAIL_PUNCT.sub('', RE_ALL_PUNCT.sub('', s)))

    return s

def mangle_text(s):
    """
    Convert segment text into the key suitable for rough matching

    Does the following conversions:
    * Replaces all numbers in forms ##; ##.##; ##.##.##...; ##,## with a special symbol (0x01)
    * Replaces all phone numbers (plus sign followed by two or more numbers separated by whitespace)
      with a special symbol (0x02)
    * Prepends special symbols to specific constructs:
        - domain names: 0x03
        - URLs: 0x04
        - e-mail addresses: 0x05
    * Lowercases the text, except in the specific constructs above
    * Removes all numbers, punctuation and whitespace:
        - from the beginning, before the first meaningful word
        - from the end, after the last meaningful word
    * Surrounds all punctuation and numbers with whitespace
    * Collapses whitespace into single spaces
    """

    fragments = []

    while True:
        m = RE_URL_OR_EMAIL.search(s)

        if m is None:
            break

        text_before = s[:m.start()]
        if text_before.strip():
            fragments.append(mangle_text_inner(text_before))

        if m.group(2) == 'www':
            prefix = '\003'
        elif m.group(1) == 'http':
            prefix = '\004'
        else:
            prefix = '\005'

        fragments.append(prefix + m.group(0))

        s = s[m.end():]

    if s.strip():
        fragments.append(mangle_text_inner(s))

    s = ' '.join(fragments)

    # split/rejoin (effectively compressing whitespace)
    words = s.split()
    s = ' '.join(words)

    return s


class Segment:
    """
    Translation memory segment representation
    """
    class NoLang(Exception):
        """
        No primary language variants found in this segment
        """
        pass

    class NoSegment(Exception):
        """
        No <seg> tag found inside the variant (<tu>)
        """
        pass

    class ComplexTags(Exception):
        """
        Some markup tags inside <seg> contain nested tags
        """
        pass

    class TagsWithText(Exception):
        """
        Some markup tags inside <seg> have text content
        """
        pass


    @classmethod
    def parse_tu(cls, tu, opts=GlobalOpts()):
        """
        Parse segment from <tu> element from XML tree
        """

        # choose TU variant in primary language defined in global options
        lang_selector = "tuv[@xml:lang='{}']".format(opts.primary_lang)
        tuv = tu.find(lang_selector, NSD)

        if tuv is None:
            raise cls.NoLang("No language found: {}".format(PRIMARY_LANG))

        # find the tag containing actual text segment
        seg = tuv.find('seg')

        if seg is None:
            raise cls.NoSegment("No text segment found")

        # extract and mangle text for rough matching index
        text = seg.text or ""

        for tag in seg:
            if len(tag):
                raise cls.ComplexTags("Nested markup tags in segment are not supported")

            tag_text = tag.text and tag.text.strip()
            if tag_text:
                raise cls.TagsWithText("Non-empty content inside markup tags is not supported")

            if tag.tail:
                text += " " + tag.tail

        text = mangle_text(text)

        # extract segment priority from properties
        for prop in tu.findall('prop'):
            if prop.attrib['type'] == 'x-ConfirmationLevel':
                confirmation_level = prop.text
                break

        else:
            confirmation_level = 'Unknown'

        # extract changed date
        changedate = tu.attrib['changedate']

        # actually create the segment
        return cls(tu, text, changedate=changedate, confirmation_level=confirmation_level)


    def compare(self, other):
        """
        If two segments (this one and the other) are equivalent, return the tuple
        containing the best match (by date and/or score) first, and the other match second.
        If two segments are not equivalent, return None.
        """
        if self.text == other.text:
            if self.priority > other.priority:
                return (self, other)
            elif self.priority < other.priority:
                return (other, self)

            if self.changedate >= other.changedate:
                return (self, other)
            else:
                return (other, self)

        return None


    def __init__(self, tu, text, changedate='00000000T000000Z', priority=0, confirmation_level='Unknown'):
        """
        Create the segment with specified data.

        Default values for all optional parameters are chosen
        in such a way that this segment has lower priority than
        the segment with the same parameter set to a real value
        """
        self.tu = tu
        self.text = text
        self.changedate = changedate
        self.confirmation_level = confirmation_level
        self.priority = PRIORITIES.get(confirmation_level, 0)


class SegmentHtml:
    DELETION_REASONS = {
        'deleted-duplicate': 'Duplicate',
        'not-deleted': '',
        'deleted-notext': 'No Text Content',
    }

    RE_NL = re.compile(r'\r?\n')
    RE_LEAD_SPACES = re.compile(r'^(\040+)')

    def _add_text(self, dest, last_tag, text):
        if not text:
            return

        for frag in self.RE_NL.split(text):
            frag = self.RE_LEAD_SPACES.sub((lambda x: '\xA0' * len(x.group(0))), frag)
            if last_tag is not None:
                last_tag.tail = frag
                last_tag = None
            else:
                br = ET.Element('br')
                dest.append(br)
                br.tail = frag


    def __init__(self, segment, deletion_reason=None, debug=False):
        div = ET.Element('div')

        deletion_reason_desc = ''
        if deletion_reason:
            try:
                desc = self.DELETION_REASONS[deletion_reason]

                if desc:
                    deletion_reason_desc = '; Deleted Because: {}'.format(desc)

                div.attrib['class'] = deletion_reason

            except KeyError:
                raise ValueError("Unknown deletion reason {}".format(deletion_reason))

        paragraph = ET.Element('p')
        paragraph.attrib['class'] = 'metadata'
        paragraph.text = 'Change Date: {}, Confirmation Level: {}{}'.format(
                segment.changedate, segment.confirmation_level, deletion_reason_desc)

        div.append(paragraph)

        for tuv in segment.tu.findall('tuv'):
            paragraph = ET.Element('p')
            seg = tuv.find('seg')

            span = ET.Element('span')
            span.attrib['class'] = 'langname'
            span.text = tuv.attrib.get('{http://www.w3.org/XML/1998/namespace}lang', 'Unknown')
            paragraph.append(span)
            self._add_text(paragraph, span, seg.text)

            for markup in seg:
                span = ET.Element('span')
                span.attrib['class'] = 'markup_' + markup.tag
                span.text = '<{}>'.format(markup.tag)
                paragraph.append(span)
                self._add_text(paragraph, span, markup.tail)

            div.append(paragraph)

        if debug:
            paragraph = ET.Element('p')
            text = segment.text
            text = text.replace('\001', '🔢').replace('\002', '☎').replace('\003', '🖥').replace('\004', '🌍').replace('\005', '📧')
            span = ET.Element('span')
            span.attrib['class'] = 'langname'
            span.text = "KEY"
            span.tail = text
            paragraph.append(span)
            div.append(paragraph)

        self.root = div

    def as_html(self):
        return self.root


class HtmlExport:
    def __init__(self):
        html = ET.Element('html')
        root = ET.ElementTree(html)

        head = ET.Element('head')
        style = ET.Element('style')
        style.text = """
span.langname {
    background-color: lightgray;
    padding-left: 0.5em;
    padding-right: 0.5em;
    margin-right: 0.5em;
    border-radius: 0.25em;
}
span.markup_ept {
    background-color: #80ffaa;
    padding-left: 0.25em;
    padding-right: 0.25em;
    margin-left: 0.1em;
    margin-right: 0.1em;
    border-radius: 0.25em;
}
span.markup_bpt {
    background-color: #ffbbbc;
    padding-left: 0.25em;
    padding-right: 0.25em;
    margin-left: 0.1em;
    margin-right: 0.1em;
    border-radius: 0.25em;
}
span.markup_ph {
    background-color: #a4adff;
    padding-left: 0.25em;
    padding-right: 0.25em;
    margin-left: 0.1em;
    margin-right: 0.1em;
    border-radius: 0.25em;
}
div {
    margin-top: 0.5em;
    margin-bottom: 0.5em;
    padding-left: 0.5em;
}
div.deleted-duplicate {
    border-left: 0.25em solid red;
    padding-left: 0.25em;
}
div.not-deleted {
    border-left: 0.25em solid lightgreen;
    padding-left: 0.25em;
}
div.deleted-notext {
    border-left: 0.25em solid #FF0000;
    padding-left: 0.25em;
}
p.metadata {
    font-style: italic;
}
p {
    margin-bottom: 0.25em;
    margin-top: 0.25em;
}
"""

        head.append(style)

        html.append(head)

        body = ET.Element('body')
        html.append(body)

        self.body = body
        self.root = root

    def to_file(self, filename):
        self.root.write(filename, encoding='utf-8', xml_declaration=True)

    def add_tag(self, tag):
        if hasattr(tag, 'as_html'):
            tag = tag.as_html()

        self.body.append(tag)


class TranslationMemory:
    """
    Translation memory representation
    """
    class NoBody:
        """
        Translation memory contains no <body> tag
        """
        pass

    class Filtered:
        filtered = None
        deleted = None
        deleted_report = None
        deleted_notext = 0
        deleted_duplicate = 0
        total = 0

        @property
        def filtered_count(self):
            return self.total - self.deleted_notext - self.deleted_duplicate

    def add_to_index(self, segment):
        """
        Add segment to rough matching index
        """
        self.segments.setdefault(segment.text, []).append(segment)

    def add(self, segment):
        """
        Add segment to TM:
        * Append its inner raw <tu> XML tag to the body tag
        * Add it to rough matching index
        """
        self.body.append(segment.tu)
        self.add_to_index(segment)

    def add_raw(self, tag):
        """
        Add raw XML tag to the body tag
        """
        self.body.append(tag)

    def _parse_segments(self):
        """
        Inner: Parse segments already in TM to Segment objects
        """
        tus = self.root.findall('./body/tu')

        skipped_lang = 0
        skipped_seg = 0
        skipped_complex = 0
        skipped_tagtext = 0

        for tu in tus:
            try:
                segment = Segment.parse_tu(tu)
                self.add_to_index(segment)

            except Segment.NoSegment:
                skipped_seg += 1

            except Segment.NoLang:
                skipped_lang += 1

            except Segment.TagsWithText:
                skipped_tagtext += 1

            except Segment.ComplexTags:
                skipped_complex += 1

        self.skipped_lang = skipped_lang
        self.skipped_seg = skipped_seg
        self.skipped_complex = skipped_complex
        self.skipped_tagtext = skipped_tagtext

    def __init__(self, root):
        """
        Create translation memory from XML root.

        Note that this function does not parse existing segments itself
        """
        self.root = root
        self.body = root.find('./body')
        if self.body is None:
            raise self.NoBody("No body in TMX tree")

        self.segments = {}

    @classmethod
    def from_file(cls, filename):
        """
        Load TM from TMX file

        This function parses segments already in TM as well
        """
        root = ET.parse(filename)

        tm = cls(root)

        tm._parse_segments()

        return tm

    def spawn_empty(self):
        """
        Create an empty TM with header cloned from this TM's header
        """
        new_root = ET.fromstring('<tmx version="1.4"><body></body></tmx>')
        new_root.insert(0, copy.deepcopy(self.root.find('./header')))

        root = ET.ElementTree(new_root)

        return type(self)(root)

    def get_rough_matches(self, segment):
        """
        Get all rough matches for the specified segment
        """
        return self.segments.get(segment.text, [])

    def iterate(self):
        """
        Iterate over all segments in rough matching index
        """
        for v in self.segments.values():
            yield from v

    def generate_filtered(self, opts=GlobalOpts()):
        """
        Generate filtered TM and deleted segments TM, as a tuple
        """
        seen = set()

        filtered = self.spawn_empty()
        deleted = self.spawn_empty()

        if opts.report:
            deleted_html = HtmlExport()
        else:
            deleted_html = None

        # an additional horizontal line will be added before first duplicate entry
        # in the HTML report to separate preceding no-text entries, if any
        notext_emitted = False

        deleted_notext = 0
        deleted_duplicate = 0
        total = 0

        for segment in self.iterate():
            total += 1

            if not segment.text:
                # segment contains no meaningful text => skip
                if opts.debug:
                    segment = copy.deepcopy(segment)
                    segment.tu.attrib['notext'] = '1'

                deleted.add(segment)
                if deleted_html:
                    deleted_html.add_tag(SegmentHtml(segment, deletion_reason='deleted-notext', debug=opts.debug))
                    notext_emitted = True

                deleted_notext += 1

                continue

            if segment in seen:
                # already processed this segment
                continue

            seen.add(segment)

            has_deleted = False

            for rough_match in self.get_rough_matches(segment):
                if rough_match in seen:
                    continue

                try:
                    segment, drop_segment = rough_match.compare(segment)

                    if opts.debug:
                        drop_segment = copy.deepcopy(drop_segment)
                        drop_segment.tu.attrib['prio'] = str(drop_segment.priority)

                    deleted.add(drop_segment)
                    seen.add(rough_match)
                    has_deleted = True

                    deleted_duplicate += 1

                    if deleted_html:
                        if notext_emitted:
                            deleted_html.add_tag(ET.Element('hr'))
                            notext_emitted = False

                        deleted_html.add_tag(SegmentHtml(drop_segment, deletion_reason='deleted-duplicate', debug=opts.debug))

                except TypeError:
                    continue

            filtered.add(segment)
            if has_deleted:
                if opts.debug:
                    segment_clone = copy.deepcopy(segment)
                    segment.tu.attrib['chosen'] = '1'
                    segment.tu.attrib['prio'] = str(segment.priority)
                    deleted.add(segment)

                    divider = ET.fromstring('<divider />')
                    deleted.add_raw(divider)

                if deleted_html:
                    deleted_html.add_tag(SegmentHtml(segment, deletion_reason='not-deleted', debug=opts.debug))
                    deleted_html.add_tag(ET.Element('hr'))

        res = self.Filtered()

        res.filtered = filtered
        res.deleted = deleted
        res.deleted_report = deleted_html
        res.deleted_duplicate = deleted_duplicate
        res.deleted_notext = deleted_notext
        res.total = total

        return res

    def to_file(self, file_name):
        """
        Write TM to a TMX file under specified name
        """
        self.root.write(file_name, encoding='utf-8', xml_declaration=True)


def process_file(filename, opts):
    """
    Process a TMX file, writing two new TMX files as a result

    Filter TMX file and write filtered TM and deleted segments TM to new TMX files.
    The output file names based on the original file name:
    If the original file is named FILE.tmx, then:
    * The filtered TM is written to FILE.filtered.tmx
    * The deleted segments TM is written to FILE.deleted.tmx
    """
    w = MessageWriter(opts)

    w.print_verbose("Loading TMX...")
    tm = TranslationMemory.from_file(filename)

    w.print_verbose("Filtering...")
    res = tm.generate_filtered(opts)

    w.print_verbose("* Deleted (Duplicate): {}".format(res.deleted_duplicate))
    w.print_verbose("* Deleted (No Text Content): {}".format(res.deleted_notext))
    w.print_verbose("* Filtered: {}".format(res.filtered_count))

    basename, ext = os.path.splitext(filename)

    w.print_verbose("Writing results...")
    res.filtered.to_file(basename + '.filtered' + ext)
    res.deleted.to_file(basename + '.deleted' + ext)

    if res.deleted_report:
        res.deleted_report.to_file(basename + '.deleted.html')

    w.print_verbose("Done.")


parser = argparse.ArgumentParser(description='Remove redundant segments from translation memory')
parser.add_argument('file', metavar='FILE', nargs='+', help='File(s) to process')
parser.add_argument('-l', '--lang', type=str, default=DEFAULT_PRIMARY_LANG, metavar='LANG_CODE',
                    help='Use specified language as primary. LANG_CODE is an ISO language/country code, e.g. "en-US"')
parser.add_argument('-r', '--report', action='store_true', default=False,
                    help='Write deleted segments report in HTML')
parser.add_argument('-v', '--verbose', action='store_true', default=False,
                    help='Show verbose progress messages')
parser.add_argument('-d', '--debug', action='store_true', default=False,
                    help='Debug mode: add special tags to deleted segment TM')
args = parser.parse_args()

opts = GlobalOpts(args)

for file in args.file:
    process_file(file, opts)
