curl --output lf.tgz https://softwarefoundations.cis.upenn.edu/lf-current/lf.tgz
curl --output plf.tgz https://softwarefoundations.cis.upenn.edu/plf-current/plf.tgz
tar -xf lf.tgz
tar -xf plf.tgz
cd lf
make
cd ../plf
make