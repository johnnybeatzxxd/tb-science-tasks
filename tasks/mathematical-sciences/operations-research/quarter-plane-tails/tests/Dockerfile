# Separate-verifier image: same base and the same Python packages as the agent image, plus pytest.
FROM python:3.12.7-slim-bookworm

RUN pip install --no-cache-dir numpy==2.1.3 scipy==1.14.1 sympy==1.13.3 mpmath==1.3.0 \
    && pip install --no-cache-dir pytest==8.4.1 pytest-json-ctrf==0.3.5

WORKDIR /root
RUN mkdir -p /root/qtails
