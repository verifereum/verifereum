all: index.html contribute.html

index.html: index.md index.css template.html verifereum-logo-big.svg verifereum-logo-small.svg
	pandoc -s --template=template.html --variable=title='' -c './index.css' index.md -o index.html

contribute.html: contribute.md index.css template.html
	pandoc -s --template=template.html --variable=title='' -c './index.css' contribute.md -o contribute.html
