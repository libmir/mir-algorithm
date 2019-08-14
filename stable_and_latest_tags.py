#!/usr/bin/python3

import semver
import functools
import subprocess

def isValid(tag):
    if not tag.startswith('v'):
        return False
    tag = tag[1:]
    try:
        return semver.match(tag, ">=0.0.0")
    except:
        return False

tags = subprocess.run(["git", "tag", "-l"], capture_output=True, text=True).stdout.split()
tags = map(lambda tag: tag[1:], filter(lambda tag: isValid(tag), tags))
tags = sorted(tags, key=functools.cmp_to_key(semver.compare))
stable_tags = list(filter(lambda tag: tag == semver.finalize_version(tag), tags))
print(stable_tags[-1])
print(tags[-1])
