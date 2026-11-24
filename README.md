# SAT Forgetting Lab

SAT에서 변수를 지우면서 중간 식을 작게 유지할 수 있을까? 같은 식을 작게 표현하기 어려울 때도 SAT 여부만 빠르게 판정할 수 있을까? 이 저장소는 두 질문을 구별해 실험 코드, 수학적 증명, Lean 정리로 조사한다. **P 대 NP는 미해결이다.**

### 가장 짧은 실험

`python -B examples.py`의 마지막 예제는 변수쌍 24개와 스위치 하나를 쓴다. 배경을 제외한 함수는 보호된 변수만 쓰는 정확한 CNF로 표현하려면 **16,777,217개 절**이 필요하다. 배경까지 포함한 SAT 문제는 배경의 극대 해 **두 개**를 검사하면 UNSAT임을 알 수 있다. 두 수치는 각각 필요한 표현 크기와 함수 평가 횟수다. [직접 판정 알고리즘과 증명](FRONTIER.md)

### 무엇을 증명했나

| 질문 | 결과 |
|---|---|
| 서로 의존하는 숨은 변수를 정확히 지울 수 있는가? | 숨은 변수의 음의 리터럴이 절마다 최대 하나인 시스템에서, 상한 규칙의 선택을 열거해 모든 남은 할당에서 정확한 CNF를 얻는다. 입력으로 열거량의 상한을 계산할 수 있고, 그만큼 절이 꼭 필요한 무한 예제도 있다. [투영 정리](THEORY.md) · [Lean 증명](Formal/Emission.lean) |
| 작은 절들만으로 함수를 전부 설명할 수 있는가? | 방향이 알려진 단조 함수에서는 단위 절 표현의 정확성을 최대 `n+2`번의 평가로 판정한다. 이항 절 표현의 정확성을 판별하는 문제는 이 저장소의 제한된 비순환 입력에서도 coNP-완전하다. [단항·이항 경계](CERTIFICATION.md) · [3-SAT 환원의 Lean 증명](Reductions/BinaryExactness.lean) |
| 소거 순서에 관계없이 중간 식을 작게 유지할 수 있는가? | 가드가 고정된 수의 포함 사슬로 주어지고 각 절의 나머지에 리터럴이 최대 두 개면, 모든 소거 순서에서 누적 표현 크기가 다항식이다. [증명과 검증기](routes/construction/README.md) |
| 보조 변수나 입력 질의는 얼마나 필요한가? | 패리티의 CNF 표현에서 절과 보조 변수 사이의 교환관계를 유도했다. 블랙박스에서는 단 한 입력에서 다른 후보들을 구별하는 데 최악에 지수 개 질의가 든다. [보조 변수 하한](routes/obstructions/README.md) · [질의 하한](routes/query-limit/README.md) |
| 일반 SAT도 풀리는가? | DIMACS CNF를 받는 완전한 판정기를 구현했다. 숨은 부분을 극성 재지정으로 dual-Horn으로 만들고 나머지 변수를 분기한다. 희소하고 연결된 입력군에서 분기 수가 지수적으로 증가한다. [알고리즘과 반례](FRONTIER.md) |
| 2-SAT 배경에 XOR 조건도 있으면? | 배경의 충돌 그래프에 크기 `k`의 정점 덮개가 있고 XOR 랭크가 `r`이면, 극대 모델마다 최대 `r`개의 함의 성분을 골라 검사하면 충분하다. 한 성분이 여러 입력의 값을 한꺼번에 바꿀 수 있다. [혼합 판정법](routes/affine-frontier/README.md) · [독립 반례 검토](routes/obstructions/affine-frontier.md) |

### 재현

Python 3.10 이상과 Lean 4.36.0을 사용한다. Python은 표준 라이브러리만 쓰며 Lean 프로젝트에는 추가 패키지가 없다.

```sh
python -B -m unittest discover -v
python -B examples.py
python -B solver_experiment.py
lake build
```

일반 DIMACS 파일은 `python -B solve_cnf.py input.cnf`로 실행한다. SAT이면 모델을 출력하고 종료 코드 10을, UNSAT이면 20을 반환한다. 선택한 `--max-patterns` 예산이 먼저 소진되면 UNKNOWN을 반환한다.

### 출처와 검증 범위

별도로 진행한 유한 그래프 회로 실험에서 적은 수의 경계 입력만으로 후보를 검사한 경험이 블랙박스 질의 실험의 동기였다. 질의 노트의 **58**은 그 비교 예산이다. SAT 예제와 입력군은 여기의 생성기로 만들었다. Lean 코드는 이 저장소의 모듈과 Lean 자체 라이브러리만 불러온다. [재현 명령과 검증 범위](VERIFICATION.md)

The [technical note](THEORY.md) gives an exact CNF projection algorithm and its policy-count bound. The [decision note](FRONTIER.md) describes a different algorithm whose cost depends on a vertex cover of the background conflict graph. Lean checks the named semantic theorems. Asymptotic complexity bounds use the written arguments; exhaustive tests cover finite inputs. No literature-priority claim is made.
