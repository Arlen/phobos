
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01//EN" "http://www.w3.org/TR/html4/strict.dtd">
<html lang="en-US">

<!--
	Copyright (c) 1999-2012 by Digital Mars
	All Rights Reserved Written by Walter Bright
	http://digitalmars.com
  -->

<head>
<meta http-equiv="content-type" content="text/html; charset=utf-8" />
<meta name="keywords" content="D programming language" />
<meta name="description" content="D Programming Language" />
<title>Bug tracker for dmd - D Programming Language</title>
<link rel="stylesheet" href="/css/codemirror.css" />
<link rel="stylesheet" type="text/css" href="css/style.css" />
<link rel="stylesheet" type="text/css" href="css/print.css" media="print" />
<script src="https://ajax.googleapis.com/ajax/libs/jquery/1.7.2/jquery.min.js" type="text/javascript"></script>
<script src="/js/codemirror.js"></script>
<script src="/js/run-main-website.js" type="text/javascript"></script>
<script src="/js/d.js"></script>
<script src="/js/run.js" type="text/javascript"></script>

<link rel="shortcut icon" href="favicon.ico" />

<script src="/js/hyphenate.js" type="text/javascript"></script>

<script type="text/javascript">
function bodyLoad()
{
	var links = document.getElementById("navigation").getElementsByTagName("a");
	for (var i = 0; i < links.length; i++)
	{
		var url = "/" + links[i].getAttribute("href");
		if (window.location.href.match(url + "\x24") == url)
		{
			var cls = links[i].getAttribute("class");
			links[i].setAttribute("class", cls ? cls + " active" : "active");
			break;
		}
	}
}
</script>
</head>

<body onLoad='bodyLoad()'>

<div id="top">
	<div id="search-box">
		<form method="get" action="http://google.com/search">
			<img src="/images/search-left.gif" width="11" height="22" /><input id="q" name="q" /><input type="image" id="search-submit" name="submit" src="/images/search-button.gif" />
			<input type="hidden" id="domains" name="domains" value="dlang.org" />
			<input type="hidden" id="sourceid" name="sourceid" value="google-search" />
			<div id="search-dropdown">
				<select id="sitesearch" name="sitesearch" size="1">
					<option value="dlang.org">Entire D Site</option>
					<option value="dlang.org/phobos">Library Reference</option>
					<option value="digitalmars.com/d/archives">Newsgroup Archives</option>
				</select>
			</div>
		</form>
	</div>
	<div id="header">
		<a id="d-language" href="/">
		<img id="logo" width="125" height="95" border="0" alt="D Logo" src="images/dlogo.png">
		D Programming Language</a>
	</div>
</div>

<!-- Generated by Ddoc from bugstats.php.dd -->



<div id="navigation">
  

<div class="navblock">
<h2><a href="index.html" title="D Programming Language">D Home</a></h2>
<ul><li><a href="overview.html" title="D language overview">Overview</a></li>
	<li><a href="comparison.html" title="D feature list">Features</a></li>
	<li><a href="download.html" title="Download a D compiler">Downloads &amp; Tools</a></li>
	<li><a href="changelog.html" title="History of changes to D">Change Log</a></li>
	<li><a href="bugstats.php" title="D issue and bug tracking system">Bug Tracker</a></li>
	<li><a href="faq.html" title="Frequently Asked Questions">FAQ</a></li>
	<li><a href="appendices.html">Appendices</a></li>
	<li><a href="acknowledgements.html" title="Thank-you to these people who have helped with D">Acknowledgments</a></li>
	<li><a href="sitemap.html" title="Documents on this site, indexed alphabetically">Sitemap</a></li>
	<li><a href="http://digitalmars.com/d/1.0/index.html" title="D Programming Language 1.0">D1 Home</a></li>
</ul>
    </div>

<div class="navblock">
<h2>Documentation</h2>
<ul>   <li><a href="http://www.amazon.com/exec/obidos/ASIN/0321635361/classicempire">Book</a></li>
	<li><a href="http://www.informit.com/articles/article.aspx?p=1381876">&nbsp;<font size=-1><span style="visibility: hidden">3</span>1.&nbsp;Tutorial</font></a></li>
	<li><a href="http://www.informit.com/articles/article.aspx?p=1609144">&nbsp;<font size=-1>13.&nbsp;Concurrency</font></a></li>

	<li><a href="language-reference.html">Language Reference</a></li>
	<li><a href="phobos/index.html">Library Reference</a></li>
	<li><a href="howtos.html" title="Helps for using D">How-tos</a></li>
	<li><a href="articles.html">Articles</a></li>
</ul>
    </div>

<div class="navblock">
<h2>Community</h2>
<ul><li><a href="http://forum.dlang.org/" title="User forums">Forums</a></li>
	<li><a href="http://github.com/D-Programming-Language" title="D on github">GitHub</a></li>
	<li><a href="http://prowiki.org/wiki4d/wiki.cgi?FrontPage" title="Wiki for the D Programming Language">Wiki</a></li>
	<li><a href="http://prowiki.org/wiki4d/wiki.cgi?ReviewQueue" title="Queue of current and upcoming standard library additions">Review Queue</a></li>
	<li><a href="http://twitter.com/#search?q=%23d_lang" title="#d_lang on twitter.com">Twitter</a></li>
	<li><a href="http://digitalmars.com/d/dlinks.html" title="External D related links">Links</a></li>
	
</ul>
    </div>
  
<div id="translate" class="tool">Translate this page:
	<div id="google_translate_element"></div><script type="text/javascript">
	function googleTranslateElementInit() {
	  new google.translate.TranslateElement({
	    pageLanguage: 'en',
	    autoDisplay: false,
	    layout: google.translate.TranslateElement.InlineLayout.SIMPLE
	  }, 'google_translate_element');
	}
	</script>
<script type="text/javascript" src="http://translate.google.com/translate_a/element.js?cb=googleTranslateElementInit"></script>
</div>
</div><!--/navigation-->
<div id="content" class='hyphenate'>
  
<div id="tools">
	<!--span id="lastupdate">Last update Sat Oct  6 01:04:13 2012
</span-->
	<a href="https://github.com/D-Programming-Language/d-programming-language.org/edit/master/bugstats.php.dd" class="tip button">
		Improve this page
		<span>
	        Quickly fork, edit online, and submit a pull request for this page.
			Requires a signed-in GitHub account. This works well for small changes.
			If you'd like to make larger changes you may want to consider using
			local clone.
		</span>
	</a>
	<a href="http://www.prowiki.org/wiki4d/wiki.cgi?DocComments/" class="tip button">
		Page wiki
		<span>
	        View or edit the community-maintained wiki page associated with this page.
		</span>
	</a>
</div>
  <h1>Bug tracker for dmd</h1>
  <center><table cellspacing=0 cellpadding=5 valign=top class=book><caption><h3>Current bugs <font size=-1><a href="http://d.puremagic.com/issues/enter_bug.cgi?product=D">[report new bug]</a></font></h3></caption><tr><td><font color=Regression, y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=regression><a href="http://d.puremagic.com/issues/buglist.cgi?y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=regression">Regression</a></font></td> <td><iframe scrolling=no frameborder=0 width="4.8em" height="1.4em" style="width:4.8em;height:1.4em;" vspace="0" hspace="0" marginwidth="0" marginheight="0" src=fetch-issue-cnt.php?y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=regression&format=table&action=wrap&ctype=csv></iframe></td></tr>
<tr><td><font color=Blocker, y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=blocker><a href="http://d.puremagic.com/issues/buglist.cgi?y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=blocker">Blocker</a></font></td> <td><iframe scrolling=no frameborder=0 width="4.8em" height="1.4em" style="width:4.8em;height:1.4em;" vspace="0" hspace="0" marginwidth="0" marginheight="0" src=fetch-issue-cnt.php?y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=blocker&format=table&action=wrap&ctype=csv></iframe></td></tr>
<tr><td><font color=Critical, y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=critical><a href="http://d.puremagic.com/issues/buglist.cgi?y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=critical">Critical</a></font></td> <td><iframe scrolling=no frameborder=0 width="4.8em" height="1.4em" style="width:4.8em;height:1.4em;" vspace="0" hspace="0" marginwidth="0" marginheight="0" src=fetch-issue-cnt.php?y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=critical&format=table&action=wrap&ctype=csv></iframe></td></tr>
<tr><td><font color=Major, y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=major><a href="http://d.puremagic.com/issues/buglist.cgi?y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=major">Major</a></font></td> <td><iframe scrolling=no frameborder=0 width="4.8em" height="1.4em" style="width:4.8em;height:1.4em;" vspace="0" hspace="0" marginwidth="0" marginheight="0" src=fetch-issue-cnt.php?y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=major&format=table&action=wrap&ctype=csv></iframe></td></tr>
<tr><td><font color=Normal, minor, or trivial, y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=normal&bug_severity=minor&bug_severity=trivial><a href="http://d.puremagic.com/issues/buglist.cgi?y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=normal&bug_severity=minor&bug_severity=trivial">Normal, minor, or trivial</a></font></td> <td><iframe scrolling=no frameborder=0 width="4.8em" height="1.4em" style="width:4.8em;height:1.4em;" vspace="0" hspace="0" marginwidth="0" marginheight="0" src=fetch-issue-cnt.php?y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=normal&bug_severity=minor&bug_severity=trivial&format=table&action=wrap&ctype=csv></iframe></td></tr>
<tr><td><font color=Enhancement, y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=enhancement><a href="http://d.puremagic.com/issues/buglist.cgi?y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=enhancement">Enhancement</a></font></td> <td><iframe scrolling=no frameborder=0 width="4.8em" height="1.4em" style="width:4.8em;height:1.4em;" vspace="0" hspace="0" marginwidth="0" marginheight="0" src=fetch-issue-cnt.php?y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=enhancement&format=table&action=wrap&ctype=csv></iframe></td></tr>
<tr><td><font color=All open, y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=normal&bug_severity=minor&bug_severity=trivial&bug_severity=regression&bug_severity=blocker&bug_severity=critical&bug_severity=major&bug_severity=enhancement><a href="http://d.puremagic.com/issues/buglist.cgi?y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=normal&bug_severity=minor&bug_severity=trivial&bug_severity=regression&bug_severity=blocker&bug_severity=critical&bug_severity=major&bug_severity=enhancement">All open</a></font></td> <td><iframe scrolling=no frameborder=0 width="4.8em" height="1.4em" style="width:4.8em;height:1.4em;" vspace="0" hspace="0" marginwidth="0" marginheight="0" src=fetch-issue-cnt.php?y_axis_field=bug_severity&query_format=report-table&product=D&bug_status=NEW&bug_status=ASSIGNED&bug_status=REOPENED&bug_severity=normal&bug_severity=minor&bug_severity=trivial&bug_severity=regression&bug_severity=blocker&bug_severity=critical&bug_severity=major&bug_severity=enhancement&format=table&action=wrap&ctype=csv></iframe></td></tr>
<tr><td><font color=All closed, y_axis_field=bug_severity&query_format=report-table&product=D&bug_severity=normal&bug_severity=minor&bug_severity=trivial&bug_severity=regression&bug_severity=blocker&bug_severity=critical&bug_severity=major&bug_severity=enhancement&bug_status=RESOLVED&bug_status=VERIFIED&bug_status=CLOSED><a href="http://d.puremagic.com/issues/buglist.cgi?y_axis_field=bug_severity&query_format=report-table&product=D&bug_severity=normal&bug_severity=minor&bug_severity=trivial&bug_severity=regression&bug_severity=blocker&bug_severity=critical&bug_severity=major&bug_severity=enhancement&bug_status=RESOLVED&bug_status=VERIFIED&bug_status=CLOSED">All closed</a></font></td> <td><iframe scrolling=no frameborder=0 width="4.8em" height="1.4em" style="width:4.8em;height:1.4em;" vspace="0" hspace="0" marginwidth="0" marginheight="0" src=fetch-issue-cnt.php?y_axis_field=bug_severity&query_format=report-table&product=D&bug_severity=normal&bug_severity=minor&bug_severity=trivial&bug_severity=regression&bug_severity=blocker&bug_severity=critical&bug_severity=major&bug_severity=enhancement&bug_status=RESOLVED&bug_status=VERIFIED&bug_status=CLOSED&format=table&action=wrap&ctype=csv></iframe></td></tr>
</table></center>

<p><center><a href="http://d.puremagic.com/issues/reports.cgi?product=D&datasets=NEW%3A&datasets=ASSIGNED%3A&datasets=REOPENED%3A&datasets=RESOLVED%3A"><img border=1 src=http://d.puremagic.com/issues/graphs/D_NEW_ASSIGNED_REOPENED_RESOLVED.png></a></center></p>


  
<div id="google_ad">
<!-- Google ad -->
<script type="text/javascript"><!--
/**/google_ad_client = "pub-5628673096434613";
/**/google_ad_width = 728;
/**/google_ad_height = 90;
/**/google_ad_format = "728x90_as";
/**/google_ad_channel ="3651639259";
/**/google_page_url = document.location;
//--></script>
<script type="text/javascript" src="http://pagead2.googlesyndication.com/pagead/show_ads.js">
</script>
</div>
</div><!--/content-->



<div id="footernav">
<a href="http://forum.dlang.org/" title="User Forums">Forums</a> |
<a href="http://www.prowiki.org/wiki4d/wiki.cgi?DocComments/" title="Read/write comments and feedback">Comments</a> |
<a href="http://digitalmars.com/advancedsearch.html" title="Search Digital Mars web site">Search</a> |
<a href="download.html" title="Download D">Downloads</a> |
<a href="/">Home</a>
</div>
<div id="copyright">

Copyright &copy; 1999-2012 by Digital Mars &reg;, All Rights Reserved |
Page generated by <a href="ddoc.html">Ddoc</a> on Sat Oct  6 01:04:13 2012

</div>
</body>
</html>
