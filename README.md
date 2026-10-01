# Threshold Ring-LWE Decryption Prototype

This repository contains the prototype code for the paper:

> **A Security Analysis: Three Pitfalls in Instantiating Threshold Ring-LWE 
> Decryption for Electronic Voting**
> 
> Hossein Hasannejad and Hesam Sharifi
> *Cryptography* (MDPI), 2026.

## Contents

- `threshold_rlwe_prototype.py`: Python implementation of the threshold 
  decryption scheme, including:
  - Base Ring-LWE encryption/decryption
  - Shamir secret sharing
  - Noise-flooded partial decryption
  - Quorum-dependent combiner verification
  - Key-recovery attack simulation

## Requirements

- Python 3.12+
- No external libraries required (uses only the Python standard library)

## Usage

Run the script directly:

```
python threshold_rlwe_prototype.py
```

## License

This code is provided for reproducibility of the results reported in the 
paper. For any other use, please contact the corresponding author.
