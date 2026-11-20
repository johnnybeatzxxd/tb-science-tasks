# Separate-verifier image: same base and the same Python packages as the agent image, plus pytest
# and an unprivileged account that runs the submitted program.
FROM python:3.12.7-slim-bookworm

ENV PYTHONDONTWRITEBYTECODE=1

RUN pip install --no-cache-dir numpy==2.1.3 scipy==1.14.1 sympy==1.13.3 mpmath==1.3.0 \
    && pip install --no-cache-dir pytest==8.4.1 pytest-json-ctrf==0.3.5 \
    && apt-get update && apt-get install -y --no-install-recommends procps \
    && rm -rf /var/lib/apt/lists/* \
    && useradd --create-home --uid 1001 --shell /usr/sbin/nologin sandbox

WORKDIR /root
RUN mkdir -p /root/qtails

# The verifier files (test.sh, test_outputs.py, checker, held-out walks and reference values).
COPY . /tests/
