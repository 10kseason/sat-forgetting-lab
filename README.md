# SAT Forgetting Lab

[![CI](https://github.com/10kseason/sat-forgetting-lab/actions/workflows/ci.yml/badge.svg)](https://github.com/10kseason/sat-forgetting-lab/actions/workflows/ci.yml)

SAT에서 변수를 지우면서 중간 식을 작게 유지할 수 있을까? 같은 식을 작게 표현하기 어려울 때도 SAT 여부만 빠르게 판정할 수 있을까? 이 저장소는 두 질문을 구별해 실험 코드, 수학적 증명, Lean 정리로 조사한다. **P 대 NP는 미해결이다.**

**[모든 해가 블록마다 6대6으로 균형인 NAE 환원](MATCHING-BALANCE.md)**

### 가장 짧은 실험

변수쌍 24개와 스위치 하나를 쓴다. **[종이]** 배경을 제외한 함수의 정확한 잔존 변수 CNF에는 **16,777,217개 절**이 필요하다. **[테스트]** `python -B examples.py`는 배경을 포함한 SAT 문제에서 극대 모델 **두 개**를 평가해 UNSAT을 출력한다. [직접 판정 알고리즘과 증명](FRONTIER.md) · [실행 예제](examples.py)

### 결과와 검증 범위

**[Lean]**은 링크한 정리를 Lean 커널로 확인한 범위다. **[테스트]**는 유한 입력에서 실행한 검증이다. **[종이]**는 문서에 적힌 수학적 증명과 복잡도 분석이다.

| 질문 | 결과와 근거 |
|---|---|
| 피벗을 하나씩 정확히 지울 수 있는가? | **[Lean]** 고정 배경 아래에서 각 꼬리를 함의하는 대표 절을 그 꼬리와 같은 극성 쪽에서 골라 소거해도, 남은 모든 할당에서 확장 가능성이 보존된다. 여러 단계를 연결해도 투영은 정확하며, 단계별 절 수 예산으로 일정 전체의 누적 절 수를 제한할 수 있다. [피벗 소거](Formal/Forgetting.lean) · [소거 일정](Formal/Schedule.lean) · [크기 상한](Formal/Size.lean) |
| 서로 의존하는 숨은 변수를 정확히 지울 수 있는가? | **[Lean]** 숨은 변수의 음의 리터럴이 절마다 최대 하나인 시스템에서, 도달 집합과 정책 열거 범위를 증명서로 주면 출력 CNF가 모든 남은 할당에서 정확하다. **[종이]** 정책 열거 횟수의 상한과 그만큼 절이 필요한 무한 입력군을 증명했다. **[테스트]** 작은 투영 결과와 숨은 변수의 확장을 완전탐색과 비교했다. [출력 정리](Formal/Emission.lean) · [투영 분석](THEORY.md) · [검증 코드](test_research.py) |
| 단항·이항 절로 함수를 전부 설명할 수 있는가? | **[Lean]** 단조 함수의 단항 표현 정확성 조건과, 3-SAT을 부호 있는 2-CNF 표현 가능성에 연결하는 의미론적 환원을 확인했다. **[종이]** 단항 검사는 최대 `n+2`번의 함수 평가를 사용한다. 이항 표현 가능성은 해당 비순환 입력에서 coNP-완전하다. [단항 증명](Reductions/UnaryExactness.lean) · [이항 환원](Reductions/BinaryExactness.lean) · [복잡도 분석](CERTIFICATION.md) |
| 넓은 절을 2-CNF 배경에 흡수할 수 있는가? | **[종이]** 넓은 절 하나를 더한 식의 2-CNF 표현 가능성을 판정한다. 여러 절에는 전체 식의 동치를 보존하는 반복 전처리로 적용한다. **[Lean]** 모델 세 개의 다수결이 원래 관계를 위반하면, 보조 변수를 존재 양화하는 2-CNF로도 그 관계를 표현할 수 없다. **[테스트]** 작은 배경식에서 단일 절 검사와 반복 흡수의 한계를 확인했다. [알고리즘과 증명](BINARY-PROMOTION.md) · [다수결 정리](Formal/ClauseMajority.lean) · [검증 코드](test_binary_promotion.py) |
| 삼항 절에서 지울 위치를 함께 고르면 SAT을 판정할 수 있는가? | **[종이]** 알려진 삼진 큐브 덮개 구성을 적용한 별도 3-CNF 판정기다. 승격 뒤 남은 삼항 절 수가 $m$일 때 일정 검사는 최대 $(3/2)^{m+o(m)}$번의 2-SAT 호출을 쓴다. **[테스트]** 블록 덮개와 작은 3-CNF의 판정 결과를 전수 검사했다. [알고리즘과 선행 연구](BINARY-PROMOTION.md#correlating-deletions-gives-a-complete-solver) · [실험 API](ternary_schedules.py) · [검증 코드](test_ternary_schedules.py) |
| CNF를 전개하지 않고 SAT을 판정할 수 있는가? | **[Lean]** 만족 가능한 2-CNF 배경과 방향이 주어진 단조 함수에서는, 배경의 쌍 충돌 그래프에서 극대 독립집합만 검사해도 충분하다. **[종이]** 정점 덮개 크기가 `k`이면 최대 `2^k`번의 함수 평가로 판정한다. **[테스트]** 작은 입력에서 완전탐색과 비교했다. [판정 동치](Reductions/FrontierDecision.lean) · [알고리즘](FRONTIER.md) · [검증 코드](test_frontier.py) |
| 소거 순서에 관계없이 중간 식을 작게 유지할 수 있는가? | **[종이]** 가드가 고정된 수의 포함 사슬로 주어지고 각 절의 본체에 리터럴이 최대 두 개면, 가드 변수를 모두 보호한 채 본체 변수만 소거하는 모든 순서에서 누적 크기가 다항식이다. **[테스트]** 작은 식에서 소거 단계별 확장 가능성을 비교했다. [증명과 검증기](routes/construction/README.md) |
| 패리티를 표현하려면 보조 변수나 절이 얼마나 필요한가? | **[종이]** 패리티를 CNF로 표현할 때 절 수와 보조 변수 수의 교환관계를 증명했다. **[테스트]** 작은 사례에서 소거 순서와 중간 식을 검증했다. [보조 변수 하한과 검증기](routes/obstructions/README.md) |
| 함수에 대한 질의는 얼마나 필요한가? | **[Lean]** 한 입력에서만 다른 두 함수에 결정 트리가 서로 다른 답을 내려면, 그 입력을 질의해야 한다. **[종이]** 명시적 CNF 인코딩을 숨긴 멤버십 오라클 모델에서 결정적·무작위 최적 질의 하한을 증명했다. **[테스트]** 작은 사례의 동일한 이항 외피와 무작위 최적 오차를 확인했다. [결정 트리 정리](Formal/QueryTrace.lean) · [질의 하한과 검증기](routes/query-limit/README.md) |
| 일반 DIMACS CNF에서 판정기는 어떻게 동작하는가? | **[종이]** 기본 판정기는 NAE 블록 복원, 2-SAT, GF(2) 패리티와 부호 있는 NAE 컷 상한을 검사하고, 필요하면 절 수가 늘지 않는 소거와 dual-Horn 분기를 수행한다. 분기 횟수에 한도를 두지 않으면 SAT 여부를 결정한다. **[테스트]** 15변수 NAE 예제에서 `--no-cut`은 할당 8,192개를 시험했고, 기본 설정은 컷 상한으로 할당 시험 없이 UNSAT을 증명했다. [기본 판정기](solve_cnf.py) · [알고리즘과 분기 반례](FRONTIER.md) · [컷 검증 코드](test_nae_cut.py) |
| 모든 해에서 블록별 균형이 보장되는 양의 NAE-3-SAT의 난이도는? | **[Lean]** 주어진 포트 배선에서 모델의 인코딩과 디코딩이 서로의 역이고, 모든 출력 모델에서 각 12정점 블록은 두 색이 6개씩이다. **[종이]** 환원은 선형성과 네 완전 매칭을 보존하고 정점 수와 삼중항 수를 각각 네 배로 늘린다. 블록별 균형이 약속된 입력의 SAT 판정은 NP-난해하다. **[테스트]** 블록의 4,096개 색칠과 작은 환원을 검사했다. [환원과 선행 연구](MATCHING-BALANCE.md) · [모델 변환 정리](Formal/BalancedSubstitution.lean) · [검증 코드](test_matching_balance.py) |
| 블록과 매칭 표기를 지운 치환도 되돌릴 수 있는가? | **[종이]** 이 치환으로 만든 입력에서 정점과 삼중항 수에 선형인 작업으로 원래 NAE 입력과 동형인 구조를 복원한다. **[테스트]** 다섯 겹 치환 후 순서를 섞은 9,216변수 입력을 할당 시험 없이 UNSAT으로 판정했고, 12,288변수 입력은 원래 식에서 SAT 모델을 확인했다. [복원 증명](MATCHING-BALANCE.md#can-we-undo-the-construction-after-removing-every-label) · [기본 판정기의 복원 코드](anonymous_blocks.py) · [검증 코드](test_anonymous_blocks.py) |
| 작은 2-SAT 검사의 실패에서 무엇을 학습할 수 있는가? | **[종이]** 한두 변수의 가정으로 짧아진 절들을 2-SAT으로 검사하고, 모순이 나면 가정을 배제하는 단위·이항 함의를 학습하는 별도 프로빙 실험이다. **[테스트]** 강제 리터럴을 찾는 가젯과 서로 다른 패리티에서 학습 결과가 같은 사례를 확인했다. [프로빙과 컷 분석](PROBING-AND-CUTS.md) · [실험 API](binary_probing.py) · [검증 코드](test_binary_probing.py) |
| 2-CNF 배경에 XOR 조건도 있으면? | **[종이]** 주어진 방향에서 단조인 함수와 XOR 랭크 `r`에 대해, 배경의 극대 모델마다 함의 그래프의 강결합 성분을 `r`개 이하로 고른 부분집합을 검사한다. 크기 `k`의 정점 덮개를 사용하면 잔존 변수 `n`개에 대해 전체 후보는 최대 $2^k\sum_{j=0}^{r}\binom{n}{j}$개다. **[테스트]** 유한 사례를 완전탐색과 비교하고 독립 검증기로 점검했다. [혼합 판정법](routes/affine-frontier/README.md) · [독립 검토](routes/obstructions/affine-frontier.md) |
| 선택형 XOR 제약도 쌍별 검사로 판정할 수 있는가? | **[Lean]** 세 단계 이상인 경로에서, 리터럴 발생마다 두 식을 연결하는 인코딩에 쌍별로 가능하지만 전체로는 불가능한 선택 집합이 존재할 조건은 원래 CNF의 만족 가능성과 같다. **[종이]** 모든 선택 집합에 대해 쌍별 검사가 충분한지 판별하는 문제는 선택기당 식 하나일 때 다항시간에 풀리며, 두 식을 허용하면 빈 배경에서도 coNP-완전하다. **[테스트]** 랭크 판정법과 인코딩을 작은 입력에서 검증했다. [의미론적 환원](Formal/GuardedPath.lean) · [랭크와 복잡도 분석](GUARDED-AFFINE.md) · [검증 코드](test_guarded_affine.py) |

### 재현

저장소 루트에서 실행한다. Python 3.10 이상과 Lean 4.36.0을 사용한다. Python은 표준 라이브러리만 쓰며 Lean 프로젝트에는 추가 패키지가 없다.

```sh
python -B -m unittest discover -v
python -B examples.py
python -B solver_experiment.py
lake build
```

일반 DIMACS 파일은 `python -B solve_cnf.py input.cnf`로 실행한다. SAT이면 모델을 출력하고 종료 코드 10을, UNSAT이면 20을 반환한다. 선택한 `--max-patterns` 예산이 먼저 소진되면 UNKNOWN을 반환한다. 비교 실행에서는 `--no-cut`으로 NAE 컷을, `--no-blocks`로 익명 블록 복원을 건너뛸 수 있다.

`lake build`에는 질의 추적 정리도 들어 있다. CI는 기본 빌드에서 Git으로 추적되는 각 Lean 소스의 컴파일 결과가 생성됐는지 확인한다. [CI 설정](.github/workflows/ci.yml)

### 출처와 검증 범위

별도로 진행한 유한 그래프 회로 실험에서 적은 수의 경계 입력만으로 후보를 검사한 경험이 블랙박스 질의 실험의 동기였다. 질의 노트의 **58**은 그 비교 예산이다. SAT 예제와 입력군은 여기의 생성기로 만들었다. Lean 코드는 이 저장소의 모듈과 Lean 자체 라이브러리만 불러온다. [관련 문헌과 비교](RELATED-WORK.md) · [검토 기록](REVIEW.md) · [재현 명령과 검증 범위](VERIFICATION.md)
