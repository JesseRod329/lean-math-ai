#!/usr/bin/env python3
"""
fetch-arxiv-papers.py
Download recent arXiv papers for theorem extraction
"""

import argparse
import json
import urllib.request
import urllib.parse
from datetime import datetime, timedelta
import time
import xml.etree.ElementTree as ET

ARXIV_API = "http://export.arxiv.org/api/query"

def fetch_arxiv_papers(categories, days_back=1, max_results=50):
    """Fetch recent papers from arXiv API"""
    
    # Calculate date range
    end_date = datetime.now()
    start_date = end_date - timedelta(days=days_back)
    
    # Build query
    cat_query = " OR ".join([f"cat:{cat}" for cat in categories])
    query_params = {
        "search_query": cat_query,
        "start": 0,
        "max_results": max_results,
        "sortBy": "submittedDate",
        "sortOrder": "descending"
    }
    
    url = f"{ARXIV_API}?{urllib.parse.urlencode(query_params)}"
    
    print(f"Fetching papers from: {url}")
    
    try:
        with urllib.request.urlopen(url, timeout=30) as response:
            data = response.read()
            
        # Parse Atom feed
        root = ET.fromstring(data)
        
        # Namespace
        ns = {
            'atom': 'http://www.w3.org/2005/Atom',
            'arxiv': 'http://arxiv.org/schemas/atom'
        }
        
        papers = []
        for entry in root.findall('atom:entry', ns):
            paper = {
                "id": entry.find('atom:id', ns).text.split('/')[-1] if entry.find('atom:id', ns) is not None else "",
                "title": entry.find('atom:title', ns).text.strip() if entry.find('atom:title', ns) is not None else "",
                "summary": entry.find('atom:summary', ns).text.strip() if entry.find('atom:summary', ns) is not None else "",
                "published": entry.find('atom:published', ns).text if entry.find('atom:published', ns) is not None else "",
                "authors": [
                    author.find('atom:name', ns).text 
                    for author in entry.findall('atom:author', ns)
                    if author.find('atom:name', ns) is not None
                ],
                "categories": [
                    cat.get('term') 
                    for cat in entry.findall('atom:category', ns)
                ],
                "pdf_link": "",
                "doi": ""
            }
            
            # Get PDF link
            for link in entry.findall('atom:link', ns):
                if link.get('title') == 'pdf':
                    paper['pdf_link'] = link.get('href', '')
                elif link.get('rel') == 'related':
                    paper['doi'] = link.get('href', '')
            
            papers.append(paper)
        
        return papers
        
    except Exception as e:
        print(f"Error fetching papers: {e}")
        return []

def main():
    parser = argparse.ArgumentParser(description="Fetch recent arXiv papers")
    parser.add_argument("--category", action="append", required=True, 
                       help="arXiv category (e.g., math.NT, math.CO)")
    parser.add_argument("--days", type=int, default=1,
                       help="Number of days back to fetch")
    parser.add_argument("--output", required=True,
                       help="Output JSON file")
    parser.add_argument("--max-results", type=int, default=50,
                       help="Maximum papers to fetch")
    
    args = parser.parse_args()
    
    print(f"Fetching papers from categories: {args.category}")
    print(f"Days back: {args.days}")
    
    papers = fetch_arxiv_papers(args.category, args.days, args.max_results)
    
    output = {
        "fetch_date": datetime.now().isoformat(),
        "categories": args.category,
        "days_back": args.days,
        "count": len(papers),
        "papers": papers
    }
    
    with open(args.output, 'w') as f:
        json.dump(output, f, indent=2)
    
    print(f"✓ Saved {len(papers)} papers to {args.output}")

if __name__ == "__main__":
    main()
