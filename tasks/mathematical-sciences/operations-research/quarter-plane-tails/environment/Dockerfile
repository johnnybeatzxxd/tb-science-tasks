FROM python:3.12.7-slim-bookworm

ENV PYTHONDONTWRITEBYTECODE=1

# Scientific Python stack available to the agent and, identically, to the program at verification.
RUN pip install --no-cache-dir numpy==2.1.3 scipy==1.14.1 sympy==1.13.3 mpmath==1.3.0

WORKDIR /root
COPY examples.json examples_output.json /root/
RUN mkdir -p /root/qtails
