all: index.html contribute.html

index.html: index.md index.css verifereum-logo-big.svg verifereum-logo-small.svg
	pandoc -s --variable=title='' -c './index.css' index.md -o index.html

contribute.html: contribute.md index.css
	pandoc -s --variable=title='' -c './index.css' contribute.md -o contribute.html
