# Builds the site's HTML from the markdown sources and deploys it with rsync.
# README.md in this directory says what the deployed site holds.

all: index.html contribute.html

index.html: index.md index.css verifereum-logo-big.svg verifereum-logo-small.svg
	pandoc -s --variable=title='' -c './index.css' index.md -o index.html

contribute.html: contribute.md index.css
	pandoc -s --variable=title='' -c './index.css' contribute.md -o contribute.html

# DEPLOY_DEST is an rsync destination, e.g. user@host:/var/www/verifereum.
# The results table (table.html, table.css, table.js) is uploaded by the test
# run, not from here, so it is excluded and left alone by --delete.
deploy: all
	test -n "$(DEPLOY_DEST)" || { echo "set DEPLOY_DEST" >&2; exit 1; }
	rsync -az --delete --exclude 'table.*' \
	  index.html contribute.html *.css *.svg ../talks "$(DEPLOY_DEST)"

clean:
	rm -f index.html contribute.html

.PHONY: all deploy clean
