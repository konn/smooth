FROM crosscompass/ihaskell-notebook:9dc7b1034d5f

USER root
RUN apt-get update -y -qq && \
  echo "deb http://apt.llvm.org/focal llvm-toolchain-focal-9 main" \
    | tee -a /etc/apt/sources.list.d/llvm.list && \
  apt-get install -y -qq wget libgmp3-dev libgsl0-dev liblapack-dev clang-9 llvm-9 llvm-9-dev libllvm9
RUN ln -s /usr/bin/opt-9 /usr/bin/opt && ln -s /usr/bin/clang-9 /usr/bin/clang && ln -s /usr/bin/llc-9 /usr/bin/llc

RUN rm -rf /var/lib/apt/lists/*

USER jovyan
ENV WORK=/home/jovyan/work

COPY stack.yaml package.yaml Setup.hs ${WORK}/

WORKDIR ${WORK}

RUN mkdir -p ${WORK}/src ${WORK}/test ${WORK}/bench ${WORK}/app

RUN stack build --only-dependencies

COPY stack-jupyter.yaml ${WORK}/stack.yaml
COPY app ${WORK}/app
COPY src ${WORK}/src
COPY test ${WORK}/test
COPY bench ${WORK}/bench
COPY README.md ChangeLog.md ${WORK}/
RUN sed -i -e 's/-Wall/-Wno-type-defaults -Wno-name-shadowing/g' ${WORK}/package.yaml
RUN sed -i -e 's/-Wall/-Wno-type-defaults -Wno-name-shadowing/g' ${WORK}/smooth.cabal
RUN stack build

COPY notebooks ${WORK}/notebooks

ENV CHOWN_HOME=yes
ENV CHOWN_HOME_OPTS=-R
CMD ["start.sh", "jupyter", "lab", "--LabApp.token=''"]
