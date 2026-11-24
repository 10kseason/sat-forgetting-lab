# SAT Forgetting Lab

SAT에서 변수 하나 또는 여러 개를 지울 때, 남은 변수의 **모든 값**에 대해 답을 보존하면서 식을 얼마나 작게 유지할 수 있을까? 이 저장소는 그 질문을 실험 코드, 종이 증명, Lean 정리로 조사한다. P 대 NP는 미해결이다.

**주요 결과.** 일정한 형태의 숨은 변수들은 서로가 서로에게 의존하는 경우에도 정확히 지울 수 있다. 출력 크기에 대한 상한을 계산했고, 그 상한만큼 절이 꼭 필요한 무한 예제를 만들었다. 반면 남은 식이 2-SAT로 정확히 표현되는지를 일반적으로 알아내는 일은 여기서 다루는 매우 제한된 입력에서도 coNP-완전하다. [정의와 증명](THEORY.md)

### 계산이 작아지는 경우

숨은 변수에 대한 음의 리터럴이 절마다 최대 하나라고 하자. 예를 들어 세 절 `(¬h ∨ a), (¬h ∨ b), (h ∨ c)`가 있으면, 남은 값이 주어졌을 때 `h`는 `a AND b`까지 켤 수 있다. 마지막 절은 `(a OR c) AND (b OR c)`가 된다. 이와 같은 치환을 서로 의존하는 여러 변수에 대해 수행할 때, 고정된 함의 배경 아래 중복되는 조건을 먼저 제거하고 각 출력 절이 실제로 참조하는 숨은 변수만 따라간다. [투영 알고리즘](forgetting.py) · [동시에 모든 숨은 변수에 맞는 선택이 존재한다는 Lean 증명](Formal/Policies.lean)

### 계산이 커지는 경우

분리된 변수쌍이 10개인 `ORᵢ(aᵢ AND bᵢ)`는 보조 변수를 쓰면 선형 크기로 표현된다. 보조 변수를 모두 지운 정확한 CNF에는 **1,024개 절**이 꼭 필요하다. 일반적으로 변수쌍이 하나 늘 때마다 필요한 절 수가 두 배가 된다. 따라서 작은 CNF를 계속 유지하는 전략에는 입력 조건이 필요하다. SAT 판정만 원하는 알고리즘은 보조 변수를 유지하거나 다른 자료구조를 사용할 수 있다. [실행 예제](examples.py)

### 2-SAT로 풀 수 있는지 알아보기

남은 변수마다 한 방향으로만 단조인 함수에서는 0인 비트가 두 개 이하인 입력을 검사해 함의되는 모든 이항 절을 계산할 수 있다. 하지만 그 절들이 원래 함수를 **완전히** 설명하는지는 별개의 문제다. 임의의 3-SAT 식을 선형 크기의 예제로 바꾸면, 변환한 함수와 이항 절이 어긋나는 입력이 존재할 때 원래 식이 만족 가능하다. 따라서 이 동치 여부를 이 클래스 전체에서 다항시간에 판정하면 P = NP가 따라온다. [의미론적 환원의 Lean 증명](Reductions/BinaryExactness.lean) · [실행 가능한 변환](binary_envelope.py)

### 재현

Python 3.10 이상과 Lean 4.36.0을 사용한다. Python은 표준 라이브러리만 쓰고 Lean 프로젝트에는 추가 패키지가 없다. 저장소 루트에서 실행한다.

```sh
python -B -m unittest -v test_research
python -B examples.py
lake build
```

The [technical note](THEORY.md) describes the projection, its policy-count bound, a tight lower bound for ordinary CNF, and the 3-SAT reduction. Lean checks the specified semantic theorems. Asymptotic complexity claims use the written arguments, and exhaustive tests cover finite instances. This project makes no priority claim for results related to resolution, dual-Horn solving or knowledge compilation.
