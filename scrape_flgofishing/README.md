a little scraping practice with beautifulsoup

example usage:

```
./scrape.py https://www.floridagofishing.com/reefs/ce-reefs-brevard-county.html
```

floridagofishing will block wget, simply change user agent:

```
wget --user-agent="Mozilla/4.0 (compatible; MSIE 6.0; Windows NT 5.1; SV1)" https://www.floridagofishing.com/reefs/ce-reefs-brevard-county.html
```

scare warning in html:

```
<!-- WHAT ARE YOU LOOKING FOR? -->
<!-- ..........................-->
<!-- Content is Copyright FloridaGoFishing.com and owned by America Go Fishing, Inc. -->
<!-- ..........................--> 
<!-- The data provided herein is copyrighted by FloridaGoFishing.com and America Go Fishing, Inc. -->
<!-- Duplication, republication or -->
<!-- redistribution of the information herein in any form whatsoever is strictly prohibited. --> 
<!-- ..........................-->
<!-- GPS Waypoint Lists of Reef Sites are derived works created by us, not public data.--> 
<!-- GPS Waypoint Lists have been SEEDED WITH SLIGHT CHANGES to thousands of records which will identify-->
<!-- any duplication, reproduction, republication, or redistribution of data.-->
<!-- ..........................-->
<!-- Any unauthorized duplication, republication, republication or redistribution of this content --> 
<!-- will be Vigorously Prosecuted. -->
```


