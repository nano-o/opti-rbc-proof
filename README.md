# Safety and liveness proof of an optimistic broadcast algorithm

See [Optimistic_RBC.pdf](./Optimistic_RBC.pdf) for a description of the protocol.

The proof has two parts: an ivy proof based on an abstract model in `opti_rbc.ivy`, and a separate proof in Isabelle/HOL that the abstract model is sound in `OptiRBC/AxiomaticDomainModel.thy`.

## Checking the Ivy proof

Install [Ivy](https://github.com/kenmcmil/ivy) in a Python 3 virtual environment and check the proof:

```bash
git clone https://github.com/kenmcmil/ivy.git
python3 -m venv ivy-venv
source ivy-venv/bin/activate
cd ivy
pip install -e .
cd ..
ivy_check seed=$RANDOM opti_rbc.ivy
```

If it takes too long then just restart `ivy_check`; you might get luckier with the next random seed...

## Checking the Isabelle proof

## Findings

- Missing assumption: n >= 2 to prevent thresholds of 0
- With n=2 and f=0, the optimistic threshold is still 0. It's obvious, but it may be worth pointing out that, in this case, we do not mean to optimistically commit on 0 echo messages.
