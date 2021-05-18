FROM node:14

RUN npm install esy

WORKDIR /opt/fstar
COPY . .
RUN esy install
RUN esy b dune build
