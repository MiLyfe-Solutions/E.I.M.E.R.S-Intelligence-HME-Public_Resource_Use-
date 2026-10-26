import V185TrunkScan22Chunk249

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2231178 : List Nat := [3, 1, 2, 4, 1, 3, 1, 2, 2, 3]
def baseStart_2231178 : Nat := 118140960795 + 2231178 * 2 ^ 59
def prefixEnd_2231178 : Nat := 4983230072969 + 3 ^ 40 * 2231178 * 2
def baseEnd_2231178 : Nat := 763777826491584493009337

theorem tailTrace_2231178 : CollatzResearch.WordTrace tailWord_2231178 prefixEnd_2231178 763777826491584493009337 := by
  unfold tailWord_2231178
  simp only [CollatzResearch.WordTrace]
  refine ⟨20344436777707658927545547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54251831407220423806788125 20344436777707658927545547)
  ·
    refine ⟨30516655166561488391318321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20344436777707658927545547 30516655166561488391318321)
    ·
      refine ⟨22887491374921116293488741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30516655166561488391318321 22887491374921116293488741)
      ·
        refine ⟨4291404632797709305029139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22887491374921116293488741 4291404632797709305029139)
        ·
          refine ⟨6437106949196563957543709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4291404632797709305029139 6437106949196563957543709)
          ·
            refine ⟨2413915105948711484078891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6437106949196563957543709 2413915105948711484078891)
            ·
              refine ⟨3620872658923067226118337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2413915105948711484078891 3620872658923067226118337)
              ·
                refine ⟨2715654494192300419588753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3620872658923067226118337 2715654494192300419588753)
                ·
                  refine ⟨2036740870644225314691565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2715654494192300419588753 2036740870644225314691565)
                  ·
                    refine ⟨763777826491584493009337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2036740870644225314691565 763777826491584493009337)
                    ·
                      rfl

theorem cell22_2231178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_2231178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231178 prefixEnd_2231178 := by exact prefixLift 2231178
  have htrace : WordTrace (prefixWord ++ tailWord_2231178) baseStart_2231178 baseEnd_2231178 := by
    simpa [prefixWord, tailWord_2231178, baseEnd_2231178] using wordTrace_append hprefix tailTrace_2231178
  have hstable : (prefixWord ++ tailWord_2231178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231178).length < 2 ^ (prefixWord ++ tailWord_2231178).sum := by decide
  have hdescent : baseEnd_2231178 < baseStart_2231178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231189 : List Nat := [1, 3, 2, 1, 1, 4, 1, 3, 3, 3]
def baseStart_2231189 : Nat := 118140960795 + 2231189 * 2 ^ 59
def prefixEnd_2231189 : Nat := 4983230072969 + 3 ^ 40 * 2231189 * 2
def baseEnd_2231189 : Nat := 763781592016384130984303

theorem tailTrace_2231189 : CollatzResearch.WordTrace tailWord_2231189 prefixEnd_2231189 763781592016384130984303 := by
  unfold tailWord_2231189
  simp only [CollatzResearch.WordTrace]
  refine ⟨81378148313790784588832621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54252098875860523059221747 81378148313790784588832621)
  ·
    refine ⟨30516805617671544220812233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81378148313790784588832621 30516805617671544220812233)
    ·
      refine ⟨22887604213253658165609175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30516805617671544220812233 22887604213253658165609175)
      ·
        refine ⟨34331406319880487248413763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22887604213253658165609175 34331406319880487248413763)
        ·
          refine ⟨51497109479820730872620645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34331406319880487248413763 51497109479820730872620645)
          ·
            refine ⟨9655708027466387038616371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51497109479820730872620645 9655708027466387038616371)
            ·
              refine ⟨14483562041199580557924557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9655708027466387038616371 14483562041199580557924557)
              ·
                refine ⟨5431335765449842709221709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14483562041199580557924557 5431335765449842709221709)
                ·
                  refine ⟨2036750912043691015958141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5431335765449842709221709 2036750912043691015958141)
                  ·
                    refine ⟨763781592016384130984303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2036750912043691015958141 763781592016384130984303)
                    ·
                      rfl

theorem cell22_2231189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_2231189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231189 prefixEnd_2231189 := by exact prefixLift 2231189
  have htrace : WordTrace (prefixWord ++ tailWord_2231189) baseStart_2231189 baseEnd_2231189 := by
    simpa [prefixWord, tailWord_2231189, baseEnd_2231189] using wordTrace_append hprefix tailTrace_2231189
  have hstable : (prefixWord ++ tailWord_2231189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231189).length < 2 ^ (prefixWord ++ tailWord_2231189).sum := by decide
  have hdescent : baseEnd_2231189 < baseStart_2231189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231240 : List Nat := [2, 1, 3, 1, 5, 1, 3, 2, 1, 3]
def baseStart_2231240 : Nat := 118140960795 + 2231240 * 2 ^ 59
def prefixEnd_2231240 : Nat := 4983230072969 + 3 ^ 40 * 2231240 * 2
def baseEnd_2231240 : Nat := 763799050358636997959147

theorem tailTrace_2231240 : CollatzResearch.WordTrace tailWord_2231240 prefixEnd_2231240 763799050358636997959147 := by
  unfold tailWord_2231240
  simp only [CollatzResearch.WordTrace]
  refine ⟨40690004218303010149469587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54253338957737346865959449 40690004218303010149469587)
  ·
    refine ⟨61035006327454515224204381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40690004218303010149469587 61035006327454515224204381)
    ·
      refine ⟨22888127372795443209076643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61035006327454515224204381 22888127372795443209076643)
      ·
        refine ⟨34332191059193164813614965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22888127372795443209076643 34332191059193164813614965)
        ·
          refine ⟨3218642911799359201276403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34332191059193164813614965 3218642911799359201276403)
          ·
            refine ⟨4827964367699038801914605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3218642911799359201276403 4827964367699038801914605)
            ·
              refine ⟨1810486637887139550717977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4827964367699038801914605 1810486637887139550717977)
              ·
                refine ⟨1357864978415354663038483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1810486637887139550717977 1357864978415354663038483)
                ·
                  refine ⟨2036797467623031994557725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1357864978415354663038483 2036797467623031994557725)
                  ·
                    refine ⟨763799050358636997959147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2036797467623031994557725 763799050358636997959147)
                    ·
                      rfl

theorem cell22_2231240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_2231240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231240 prefixEnd_2231240 := by exact prefixLift 2231240
  have htrace : WordTrace (prefixWord ++ tailWord_2231240) baseStart_2231240 baseEnd_2231240 := by
    simpa [prefixWord, tailWord_2231240, baseEnd_2231240] using wordTrace_append hprefix tailTrace_2231240
  have hstable : (prefixWord ++ tailWord_2231240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231240).length < 2 ^ (prefixWord ++ tailWord_2231240).sum := by decide
  have hdescent : baseEnd_2231240 < baseStart_2231240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231253 : List Nat := [1, 3, 2, 3, 3, 2, 2, 1, 5]
def baseStart_2231253 : Nat := 118140960795 + 2231253 * 2 ^ 59
def prefixEnd_2231253 : Nat := 4983230072969 + 3 ^ 40 * 2231253 * 2
def baseEnd_2231253 : Nat := 254601166841436432461369

theorem tailTrace_2231253 : CollatzResearch.WordTrace tailWord_2231253 prefixEnd_2231253 254601166841436432461369 := by
  unfold tailWord_2231253
  simp only [CollatzResearch.WordTrace]
  refine ⟨81380482585558923519162413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54253655057039282346108275 81380482585558923519162413)
  ·
    refine ⟨30517680969584596319685905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81380482585558923519162413 30517680969584596319685905)
    ·
      refine ⟨22888260727188447239764429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30517680969584596319685905 22888260727188447239764429)
      ·
        refine ⟨8583097772695667714911661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22888260727188447239764429 8583097772695667714911661)
        ·
          refine ⟨3218661664760875393091873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8583097772695667714911661 3218661664760875393091873)
          ·
            refine ⟨2413996248570656544818905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3218661664760875393091873 2413996248570656544818905)
            ·
              refine ⟨1810497186427992408614179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2413996248570656544818905 1810497186427992408614179)
              ·
                refine ⟨2715745779641988612921269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1810497186427992408614179 2715745779641988612921269)
                ·
                  refine ⟨254601166841436432461369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2715745779641988612921269 254601166841436432461369)
                  ·
                    rfl

theorem cell22_2231253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_2231253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231253 prefixEnd_2231253 := by exact prefixLift 2231253
  have htrace : WordTrace (prefixWord ++ tailWord_2231253) baseStart_2231253 baseEnd_2231253 := by
    simpa [prefixWord, tailWord_2231253, baseEnd_2231253] using wordTrace_append hprefix tailTrace_2231253
  have hstable : (prefixWord ++ tailWord_2231253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231253).length < 2 ^ (prefixWord ++ tailWord_2231253).sum := by decide
  have hdescent : baseEnd_2231253 < baseStart_2231253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231279 : List Nat := [1, 1, 2, 1, 4, 4, 1, 2, 1, 5]
def baseStart_2231279 : Nat := 118140960795 + 2231279 * 2 ^ 59
def prefixEnd_2231279 : Nat := 4983230072969 + 3 ^ 40 * 2231279 * 2
def baseEnd_2231279 : Nat := 763812400855653896234027

theorem tailTrace_2231279 : CollatzResearch.WordTrace tailWord_2231279 prefixEnd_2231279 763812400855653896234027 := by
  unfold tailWord_2231279
  simp only [CollatzResearch.WordTrace]
  refine ⟨81381430883464729959608891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54254287255643153306405927 81381430883464729959608891)
  ·
    refine ⟨122072146325197094939413337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81381430883464729959608891 122072146325197094939413337)
    ·
      refine ⟨91554109743897821204560003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122072146325197094939413337 91554109743897821204560003)
      ·
        refine ⟨137331164615846731806840005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91554109743897821204560003 137331164615846731806840005)
        ·
          refine ⟨25749593365471262213782501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137331164615846731806840005 25749593365471262213782501)
          ·
            refine ⟨4828048756025861665084219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25749593365471262213782501 4828048756025861665084219)
            ·
              refine ⟨7242073134038792497626329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4828048756025861665084219 7242073134038792497626329)
              ·
                refine ⟨5431554850529094373219747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7242073134038792497626329 5431554850529094373219747)
                ·
                  refine ⟨8147332275793641559829621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5431554850529094373219747 8147332275793641559829621)
                  ·
                    refine ⟨763812400855653896234027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8147332275793641559829621 763812400855653896234027)
                    ·
                      rfl

theorem cell22_2231279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_2231279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231279 prefixEnd_2231279 := by exact prefixLift 2231279
  have htrace : WordTrace (prefixWord ++ tailWord_2231279) baseStart_2231279 baseEnd_2231279 := by
    simpa [prefixWord, tailWord_2231279, baseEnd_2231279] using wordTrace_append hprefix tailTrace_2231279
  have hstable : (prefixWord ++ tailWord_2231279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231279).length < 2 ^ (prefixWord ++ tailWord_2231279).sum := by decide
  have hdescent : baseEnd_2231279 < baseStart_2231279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231292 : List Nat := [2, 2, 2, 1, 2, 13]
def baseStart_2231292 : Nat := 118140960795 + 2231292 * 2 ^ 59
def prefixEnd_2231292 : Nat := 4983230072969 + 3 ^ 40 * 2231292 * 2
def baseEnd_2231292 : Nat := 9429837666929953032827

theorem tailTrace_2231292 : CollatzResearch.WordTrace tailWord_2231292 prefixEnd_2231292 9429837666929953032827 := by
  unfold tailWord_2231292
  simp only [CollatzResearch.WordTrace]
  refine ⟨40690952516208816589916065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54254603354945088786554753 40690952516208816589916065)
  ·
    refine ⟨30518214387156612442437049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40690952516208816589916065 30518214387156612442437049)
    ·
      refine ⟨22888660790367459331827787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30518214387156612442437049 22888660790367459331827787)
      ·
        refine ⟨34332991185551188997741681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22888660790367459331827787 34332991185551188997741681)
        ·
          refine ⟨25749743389163391748306261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34332991185551188997741681 25749743389163391748306261)
          ·
            refine ⟨9429837666929953032827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 25749743389163391748306261 9429837666929953032827)
            ·
              rfl

theorem cell22_2231292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 13].length) (baseStart_2231292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231292 prefixEnd_2231292 := by exact prefixLift 2231292
  have htrace : WordTrace (prefixWord ++ tailWord_2231292) baseStart_2231292 baseEnd_2231292 := by
    simpa [prefixWord, tailWord_2231292, baseEnd_2231292] using wordTrace_append hprefix tailTrace_2231292
  have hstable : (prefixWord ++ tailWord_2231292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231292).length < 2 ^ (prefixWord ++ tailWord_2231292).sum := by decide
  have hdescent : baseEnd_2231292 < baseStart_2231292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231358 : List Nat := [4, 2, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_2231358 : Nat := 118140960795 + 2231358 * 2 ^ 59
def prefixEnd_2231358 : Nat := 4983230072969 + 3 ^ 40 * 2231358 * 2
def baseEnd_2231358 : Nat := 763839444170124023508785

theorem tailTrace_2231358 : CollatzResearch.WordTrace tailWord_2231358 prefixEnd_2231358 763839444170124023508785 := by
  unfold tailWord_2231358
  simp only [CollatzResearch.WordTrace]
  refine ⟨10173039031272315806466841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54256208166785684301156485 10173039031272315806466841)
  ·
    refine ⟨7629779273454236854850131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10173039031272315806466841 7629779273454236854850131)
    ·
      refine ⟨11444668910181355282275197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7629779273454236854850131 11444668910181355282275197)
      ·
        refine ⟨4291750841318008230853199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11444668910181355282275197 4291750841318008230853199)
        ·
          refine ⟨6437626261977012346279799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4291750841318008230853199 6437626261977012346279799)
          ·
            refine ⟨9656439392965518519419699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6437626261977012346279799 9656439392965518519419699)
            ·
              refine ⟨14484659089448277779129549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9656439392965518519419699 14484659089448277779129549)
              ·
                refine ⟨5431747158543104167173581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14484659089448277779129549 5431747158543104167173581)
                ·
                  refine ⟨2036905184453664062690093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5431747158543104167173581 2036905184453664062690093)
                  ·
                    refine ⟨763839444170124023508785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2036905184453664062690093 763839444170124023508785)
                    ·
                      rfl

theorem cell22_2231358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_2231358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231358 prefixEnd_2231358 := by exact prefixLift 2231358
  have htrace : WordTrace (prefixWord ++ tailWord_2231358) baseStart_2231358 baseEnd_2231358 := by
    simpa [prefixWord, tailWord_2231358, baseEnd_2231358] using wordTrace_append hprefix tailTrace_2231358
  have hstable : (prefixWord ++ tailWord_2231358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231358).length < 2 ^ (prefixWord ++ tailWord_2231358).sum := by decide
  have hdescent : baseEnd_2231358 < baseStart_2231358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231401 : List Nat := [1, 2, 1, 1, 1, 6, 2, 3, 1, 4]
def baseStart_2231401 : Nat := 118140960795 + 2231401 * 2 ^ 59
def prefixEnd_2231401 : Nat := 4983230072969 + 3 ^ 40 * 2231401 * 2
def baseEnd_2231401 : Nat := 763854163948886244683653

theorem tailTrace_2231401 : CollatzResearch.WordTrace tailWord_2231401 prefixEnd_2231401 763854163948886244683653 := by
  unfold tailWord_2231401
  simp only [CollatzResearch.WordTrace]
  refine ⟨81385880589022744795550057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54257253726015163197033371 81385880589022744795550057)
  ·
    refine ⟨61039410441767058596662543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81385880589022744795550057 61039410441767058596662543)
    ·
      refine ⟨91559115662650587894993815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61039410441767058596662543 91559115662650587894993815)
      ·
        refine ⟨137338673493975881842490723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91559115662650587894993815 137338673493975881842490723)
        ·
          refine ⟨206008010240963822763736085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137338673493975881842490723 206008010240963822763736085)
          ·
            refine ⟨9656625480045179192050129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 206008010240963822763736085 9656625480045179192050129)
            ·
              refine ⟨7242469110033884394037597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9656625480045179192050129 7242469110033884394037597)
              ·
                refine ⟨2715925916262706647764099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7242469110033884394037597 2715925916262706647764099)
                ·
                  refine ⟨4073888874394059971646149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2715925916262706647764099 4073888874394059971646149)
                  ·
                    refine ⟨763854163948886244683653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4073888874394059971646149 763854163948886244683653)
                    ·
                      rfl

theorem cell22_2231401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 4].length) (baseStart_2231401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231401 prefixEnd_2231401 := by exact prefixLift 2231401
  have htrace : WordTrace (prefixWord ++ tailWord_2231401) baseStart_2231401 baseEnd_2231401 := by
    simpa [prefixWord, tailWord_2231401, baseEnd_2231401] using wordTrace_append hprefix tailTrace_2231401
  have hstable : (prefixWord ++ tailWord_2231401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231401).length < 2 ^ (prefixWord ++ tailWord_2231401).sum := by decide
  have hdescent : baseEnd_2231401 < baseStart_2231401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231416 : List Nat := [2, 1, 2, 1, 1, 1, 4, 6, 4]
def baseStart_2231416 : Nat := 118140960795 + 2231416 * 2 ^ 59
def prefixEnd_2231416 : Nat := 4983230072969 + 3 ^ 40 * 2231416 * 2
def baseEnd_2231416 : Nat := 254619766251810401852869

theorem tailTrace_2231416 : CollatzResearch.WordTrace tailWord_2231416 prefixEnd_2231416 254619766251810401852869 := by
  unfold tailWord_2231416
  simp only [CollatzResearch.WordTrace]
  refine ⟨40693213841984201178673051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54257618455978934904897401 40693213841984201178673051)
  ·
    refine ⟨61039820762976301768009577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40693213841984201178673051 61039820762976301768009577)
    ·
      refine ⟨45779865572232226326007183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61039820762976301768009577 45779865572232226326007183)
      ·
        refine ⟨68669798358348339489010775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45779865572232226326007183 68669798358348339489010775)
        ·
          refine ⟨103004697537522509233516163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68669798358348339489010775 103004697537522509233516163)
          ·
            refine ⟨154507046306283763850274245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103004697537522509233516163 154507046306283763850274245)
            ·
              refine ⟨28970071182428205721926421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154507046306283763850274245 28970071182428205721926421)
              ·
                refine ⟨1357972086676322143215301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28970071182428205721926421 1357972086676322143215301)
                ·
                  refine ⟨254619766251810401852869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1357972086676322143215301 254619766251810401852869)
                  ·
                    rfl

theorem cell22_2231416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 4].length) (baseStart_2231416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231416 prefixEnd_2231416 := by exact prefixLift 2231416
  have htrace : WordTrace (prefixWord ++ tailWord_2231416) baseStart_2231416 baseEnd_2231416 := by
    simpa [prefixWord, tailWord_2231416, baseEnd_2231416] using wordTrace_append hprefix tailTrace_2231416
  have hstable : (prefixWord ++ tailWord_2231416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231416).length < 2 ^ (prefixWord ++ tailWord_2231416).sum := by decide
  have hdescent : baseEnd_2231416 < baseStart_2231416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231422 : List Nat := [4, 2, 4, 1, 1, 1, 1, 3, 5]
def baseStart_2231422 : Nat := 118140960795 + 2231422 * 2 ^ 59
def prefixEnd_2231422 : Nat := 4983230072969 + 3 ^ 40 * 2231422 * 2
def baseEnd_2231422 : Nat := 254620450892683063302863

theorem tailTrace_2231422 : CollatzResearch.WordTrace tailWord_2231422 prefixEnd_2231422 254620450892683063302863 := by
  unfold tailWord_2231422
  simp only [CollatzResearch.WordTrace]
  refine ⟨10173330815243333172758065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54257764347964443588043013 10173330815243333172758065)
  ·
    refine ⟨7629998111432499879568549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10173330815243333172758065 7629998111432499879568549)
    ·
      refine ⟨1430624645893593727419103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7629998111432499879568549 1430624645893593727419103)
      ·
        refine ⟨2145936968840390591128655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1430624645893593727419103 2145936968840390591128655)
        ·
          refine ⟨3218905453260585886692983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2145936968840390591128655 3218905453260585886692983)
          ·
            refine ⟨4828358179890878830039475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3218905453260585886692983 4828358179890878830039475)
            ·
              refine ⟨7242537269836318245059213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4828358179890878830039475 7242537269836318245059213)
              ·
                refine ⟨2715951476188619341897205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7242537269836318245059213 2715951476188619341897205)
                ·
                  refine ⟨254620450892683063302863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2715951476188619341897205 254620450892683063302863)
                  ·
                    rfl

theorem cell22_2231422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_2231422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231422 prefixEnd_2231422 := by exact prefixLift 2231422
  have htrace : WordTrace (prefixWord ++ tailWord_2231422) baseStart_2231422 baseEnd_2231422 := by
    simpa [prefixWord, tailWord_2231422, baseEnd_2231422] using wordTrace_append hprefix tailTrace_2231422
  have hstable : (prefixWord ++ tailWord_2231422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231422).length < 2 ^ (prefixWord ++ tailWord_2231422).sum := by decide
  have hdescent : baseEnd_2231422 < baseStart_2231422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231463 : List Nat := [1, 1, 6, 2, 1, 1, 2, 2, 2, 4]
def baseStart_2231463 : Nat := 118140960795 + 2231463 * 2 ^ 59
def prefixEnd_2231463 : Nat := 4983230072969 + 3 ^ 40 * 2231463 * 2
def baseEnd_2231463 : Nat := 763875387815938749633463

theorem tailTrace_2231463 : CollatzResearch.WordTrace tailWord_2231463 prefixEnd_2231463 763875387815938749633463 := by
  unfold tailWord_2231463
  simp only [CollatzResearch.WordTrace]
  refine ⟨81388141914798129384307043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54258761276532086256204695 81388141914798129384307043)
  ·
    refine ⟨122082212872197194076460565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81388141914798129384307043 122082212872197194076460565)
    ·
      refine ⟨5722603728384243472334089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 122082212872197194076460565 5722603728384243472334089)
      ·
        refine ⟨4291952796288182604250567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5722603728384243472334089 4291952796288182604250567)
        ·
          refine ⟨6437929194432273906375851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4291952796288182604250567 6437929194432273906375851)
          ·
            refine ⟨9656893791648410859563777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6437929194432273906375851 9656893791648410859563777)
            ·
              refine ⟨7242670343736308144672833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9656893791648410859563777 7242670343736308144672833)
              ·
                refine ⟨5432002757802231108504625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7242670343736308144672833 5432002757802231108504625)
                ·
                  refine ⟨4074002068351673331378469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5432002757802231108504625 4074002068351673331378469)
                  ·
                    refine ⟨763875387815938749633463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4074002068351673331378469 763875387815938749633463)
                    ·
                      rfl

theorem cell22_2231463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_2231463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231463 prefixEnd_2231463 := by exact prefixLift 2231463
  have htrace : WordTrace (prefixWord ++ tailWord_2231463) baseStart_2231463 baseEnd_2231463 := by
    simpa [prefixWord, tailWord_2231463, baseEnd_2231463] using wordTrace_append hprefix tailTrace_2231463
  have hstable : (prefixWord ++ tailWord_2231463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231463).length < 2 ^ (prefixWord ++ tailWord_2231463).sum := by decide
  have hdescent : baseEnd_2231463 < baseStart_2231463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231506 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 7]
def baseStart_2231506 : Nat := 118140960795 + 2231506 * 2 ^ 59
def prefixEnd_2231506 : Nat := 4983230072969 + 3 ^ 40 * 2231506 * 2
def baseEnd_2231506 : Nat := 254630035864900323602777

theorem tailTrace_2231506 : CollatzResearch.WordTrace tailWord_2231506 prefixEnd_2231506 254630035864900323602777 := by
  unfold tailWord_2231506
  simp only [CollatzResearch.WordTrace]
  refine ⟨20347427563410586932030593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54259806835761565152081581 20347427563410586932030593)
  ·
    refine ⟨15260570672557940199022945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20347427563410586932030593 15260570672557940199022945)
    ·
      refine ⟨11445428004418455149267209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15260570672557940199022945 11445428004418455149267209)
      ·
        refine ⟨8584071003313841361950407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11445428004418455149267209 8584071003313841361950407)
        ·
          refine ⟨12876106504970762042925611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8584071003313841361950407 12876106504970762042925611)
          ·
            refine ⟨19314159757456143064388417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12876106504970762042925611 19314159757456143064388417)
            ·
              refine ⟨14485619818092107298291313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19314159757456143064388417 14485619818092107298291313)
              ·
                refine ⟨10864214863569080473718485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14485619818092107298291313 10864214863569080473718485)
                ·
                  refine ⟨254630035864900323602777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10864214863569080473718485 254630035864900323602777)
                  ·
                    rfl

theorem cell22_2231506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_2231506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231506 prefixEnd_2231506 := by exact prefixLift 2231506
  have htrace : WordTrace (prefixWord ++ tailWord_2231506) baseStart_2231506 baseEnd_2231506 := by
    simpa [prefixWord, tailWord_2231506, baseEnd_2231506] using wordTrace_append hprefix tailTrace_2231506
  have hstable : (prefixWord ++ tailWord_2231506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231506).length < 2 ^ (prefixWord ++ tailWord_2231506).sum := by decide
  have hdescent : baseEnd_2231506 < baseStart_2231506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231521 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 2, 5]
def baseStart_2231521 : Nat := 118140960795 + 2231521 * 2 ^ 59
def prefixEnd_2231521 : Nat := 4983230072969 + 3 ^ 40 * 2231521 * 2
def baseEnd_2231521 : Nat := 763895242401245931683285

theorem tailTrace_2231521 : CollatzResearch.WordTrace tailWord_2231521 prefixEnd_2231521 763895242401245931683285 := by
  unfold tailWord_2231521
  simp only [CollatzResearch.WordTrace]
  refine ⟨81390257348588005289918417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54260171565725336859945611 81390257348588005289918417)
  ·
    refine ⟨61042693011441003967438813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81390257348588005289918417 61042693011441003967438813)
    ·
      refine ⟨22891009879290376487789555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61042693011441003967438813 22891009879290376487789555)
      ·
        refine ⟨34336514818935564731684333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22891009879290376487789555 34336514818935564731684333)
        ·
          refine ⟨12876193057100836774381625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34336514818935564731684333 12876193057100836774381625)
          ·
            refine ⟨9657144792825627580786219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12876193057100836774381625 9657144792825627580786219)
            ·
              refine ⟨14485717189238441371179329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9657144792825627580786219 14485717189238441371179329)
              ·
                refine ⟨10864287891928831028384497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14485717189238441371179329 10864287891928831028384497)
                ·
                  refine ⟨8148215918946623271288373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10864287891928831028384497 8148215918946623271288373)
                  ·
                    refine ⟨763895242401245931683285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8148215918946623271288373 763895242401245931683285)
                    ·
                      rfl

theorem cell22_2231521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_2231521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231521 prefixEnd_2231521 := by exact prefixLift 2231521
  have htrace : WordTrace (prefixWord ++ tailWord_2231521) baseStart_2231521 baseEnd_2231521 := by
    simpa [prefixWord, tailWord_2231521, baseEnd_2231521] using wordTrace_append hprefix tailTrace_2231521
  have hstable : (prefixWord ++ tailWord_2231521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231521).length < 2 ^ (prefixWord ++ tailWord_2231521).sum := by decide
  have hdescent : baseEnd_2231521 < baseStart_2231521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231551 : List Nat := [1, 1, 2, 2, 1, 5, 2, 2, 6]
def baseStart_2231551 : Nat := 118140960795 + 2231551 * 2 ^ 59
def prefixEnd_2231551 : Nat := 4983230072969 + 3 ^ 40 * 2231551 * 2
def baseEnd_2231551 : Nat := 254635170671445284477731

theorem tailTrace_2231551 : CollatzResearch.WordTrace tailWord_2231551 prefixEnd_2231551 254635170671445284477731 := by
  unfold tailWord_2231551
  simp only [CollatzResearch.WordTrace]
  refine ⟨81391351538479320413510507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54260901025652880275673671 81391351538479320413510507)
  ·
    refine ⟨122087027307718980620265761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81391351538479320413510507 122087027307718980620265761)
    ·
      refine ⟨91565270480789235465199321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122087027307718980620265761 91565270480789235465199321)
      ·
        refine ⟨68673952860591926598899491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91565270480789235465199321 68673952860591926598899491)
        ·
          refine ⟨103010929290887889898349237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68673952860591926598899491 103010929290887889898349237)
          ·
            refine ⟨9657274621020739677970241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103010929290887889898349237 9657274621020739677970241)
            ·
              refine ⟨7242955965765554758477681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9657274621020739677970241 7242955965765554758477681)
              ·
                refine ⟨5432216974324166068858261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7242955965765554758477681 5432216974324166068858261)
                ·
                  refine ⟨254635170671445284477731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5432216974324166068858261 254635170671445284477731)
                  ·
                    rfl

theorem cell22_2231551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 6].length) (baseStart_2231551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231551 prefixEnd_2231551 := by exact prefixLift 2231551
  have htrace : WordTrace (prefixWord ++ tailWord_2231551) baseStart_2231551 baseEnd_2231551 := by
    simpa [prefixWord, tailWord_2231551, baseEnd_2231551] using wordTrace_append hprefix tailTrace_2231551
  have hstable : (prefixWord ++ tailWord_2231551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231551).length < 2 ^ (prefixWord ++ tailWord_2231551).sum := by decide
  have hdescent : baseEnd_2231551 < baseStart_2231551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231553 : List Nat := [1, 2, 4, 1, 1, 3, 1, 4, 1, 4]
def baseStart_2231553 : Nat := 118140960795 + 2231553 * 2 ^ 59
def prefixEnd_2231553 : Nat := 4983230072969 + 3 ^ 40 * 2231553 * 2
def baseEnd_2231553 : Nat := 763906196655208514883187

theorem tailTrace_2231553 : CollatzResearch.WordTrace tailWord_2231553 prefixEnd_2231553 763906196655208514883187 := by
  unfold tailWord_2231553
  simp only [CollatzResearch.WordTrace]
  refine ⟨81391424484472074755083313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54260949656314716503388875 81391424484472074755083313)
  ·
    refine ⟨61043568363354056066312485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81391424484472074755083313 61043568363354056066312485)
    ·
      refine ⟨11445669068128885512433591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61043568363354056066312485 11445669068128885512433591)
      ·
        refine ⟨17168503602193328268650387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11445669068128885512433591 17168503602193328268650387)
        ·
          refine ⟨25752755403289992402975581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17168503602193328268650387 25752755403289992402975581)
          ·
            refine ⟨9657283276233747151115843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25752755403289992402975581 9657283276233747151115843)
            ·
              refine ⟨14485924914350620726673765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9657283276233747151115843 14485924914350620726673765)
              ·
                refine ⟨2716110921440741386251331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14485924914350620726673765 2716110921440741386251331)
                ·
                  refine ⟨4074166382161112079376997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2716110921440741386251331 4074166382161112079376997)
                  ·
                    refine ⟨763906196655208514883187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4074166382161112079376997 763906196655208514883187)
                    ·
                      rfl

theorem cell22_2231553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_2231553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231553 prefixEnd_2231553 := by exact prefixLift 2231553
  have htrace : WordTrace (prefixWord ++ tailWord_2231553) baseStart_2231553 baseEnd_2231553 := by
    simpa [prefixWord, tailWord_2231553, baseEnd_2231553] using wordTrace_append hprefix tailTrace_2231553
  have hstable : (prefixWord ++ tailWord_2231553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231553).length < 2 ^ (prefixWord ++ tailWord_2231553).sum := by decide
  have hdescent : baseEnd_2231553 < baseStart_2231553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231626 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 4, 6]
def baseStart_2231626 : Nat := 118140960795 + 2231626 * 2 ^ 59
def prefixEnd_2231626 : Nat := 4983230072969 + 3 ^ 40 * 2231626 * 2
def baseEnd_2231626 : Nat := 763931186047060657807963

theorem tailTrace_2231626 : CollatzResearch.WordTrace tailWord_2231626 prefixEnd_2231626 763931186047060657807963 := by
  unfold tailWord_2231626
  simp only [CollatzResearch.WordTrace]
  refine ⟨20348521753301902055622683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54262724675471738814993821 20348521753301902055622683)
  ·
    refine ⟨30522782629952853083434025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20348521753301902055622683 30522782629952853083434025)
    ·
      refine ⟨22892086972464639812575519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30522782629952853083434025 22892086972464639812575519)
      ·
        refine ⟨34338130458696959718863279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22892086972464639812575519 34338130458696959718863279)
        ·
          refine ⟨51507195688045439578294919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34338130458696959718863279 51507195688045439578294919)
          ·
            refine ⟨77260793532068159367442379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51507195688045439578294919 77260793532068159367442379)
            ·
              refine ⟨115891190298102239051163569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77260793532068159367442379 115891190298102239051163569)
              ·
                refine ⟨86918392723576679288372677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115891190298102239051163569 86918392723576679288372677)
                ·
                  refine ⟨16297198635670627366569877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86918392723576679288372677 16297198635670627366569877)
                  ·
                    refine ⟨763931186047060657807963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16297198635670627366569877 763931186047060657807963)
                    ·
                      rfl

theorem cell22_2231626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_2231626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231626 prefixEnd_2231626 := by exact prefixLift 2231626
  have htrace : WordTrace (prefixWord ++ tailWord_2231626) baseStart_2231626 baseEnd_2231626 := by
    simpa [prefixWord, tailWord_2231626, baseEnd_2231626] using wordTrace_append hprefix tailTrace_2231626
  have hstable : (prefixWord ++ tailWord_2231626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231626).length < 2 ^ (prefixWord ++ tailWord_2231626).sum := by decide
  have hdescent : baseEnd_2231626 < baseStart_2231626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231641 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 7]
def baseStart_2231641 : Nat := 118140960795 + 2231641 * 2 ^ 59
def prefixEnd_2231641 : Nat := 4983230072969 + 3 ^ 40 * 2231641 * 2
def baseEnd_2231641 : Nat := 254645440284535206227639

theorem tailTrace_2231641 : CollatzResearch.WordTrace tailWord_2231641 prefixEnd_2231641 254645440284535206227639 := by
  unfold tailWord_2231641
  simp only [CollatzResearch.WordTrace]
  refine ⟨81394634108153265784286777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54263089405435510522857851 81394634108153265784286777)
  ·
    refine ⟨61045975581114949338215083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81394634108153265784286777 61045975581114949338215083)
    ·
      refine ⟨91568963371672424007322625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61045975581114949338215083 91568963371672424007322625)
      ·
        refine ⟨68676722528754318005491969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91568963371672424007322625 68676722528754318005491969)
        ·
          refine ⟨51507541896565738504118977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68676722528754318005491969 51507541896565738504118977)
          ·
            refine ⟨38630656422424303878089233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51507541896565738504118977 38630656422424303878089233)
            ·
              refine ⟨28972992316818227908566925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38630656422424303878089233 28972992316818227908566925)
              ·
                refine ⟨10864872118806835465712597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28972992316818227908566925 10864872118806835465712597)
                ·
                  refine ⟨254645440284535206227639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10864872118806835465712597 254645440284535206227639)
                  ·
                    rfl

theorem cell22_2231641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 7].length) (baseStart_2231641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231641 prefixEnd_2231641 := by exact prefixLift 2231641
  have htrace : WordTrace (prefixWord ++ tailWord_2231641) baseStart_2231641 baseEnd_2231641 := by
    simpa [prefixWord, tailWord_2231641, baseEnd_2231641] using wordTrace_append hprefix tailTrace_2231641
  have hstable : (prefixWord ++ tailWord_2231641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231641).length < 2 ^ (prefixWord ++ tailWord_2231641).sum := by decide
  have hdescent : baseEnd_2231641 < baseStart_2231641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231769 : List Nat := [1, 2, 1, 2, 4, 4, 2, 1, 2, 3]
def baseStart_2231769 : Nat := 118140960795 + 2231769 * 2 ^ 59
def prefixEnd_2231769 : Nat := 4983230072969 + 3 ^ 40 * 2231769 * 2
def baseEnd_2231769 : Nat := 763980137869455951482525

theorem tailTrace_2231769 : CollatzResearch.WordTrace tailWord_2231769 prefixEnd_2231769 763980137869455951482525 := by
  unfold tailWord_2231769
  simp only [CollatzResearch.WordTrace]
  refine ⟨81399302651689543644946361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54266201767793029096630907 81399302651689543644946361)
  ·
    refine ⟨61049476988767157733709771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81399302651689543644946361 61049476988767157733709771)
    ·
      refine ⟨91574215483150736600564657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61049476988767157733709771 91574215483150736600564657)
      ·
        refine ⟨68680661612363052450423493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91574215483150736600564657 68680661612363052450423493)
        ·
          refine ⟨12877624052318072334454405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68680661612363052450423493 12877624052318072334454405)
          ·
            refine ⟨2414554509809638562710201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12877624052318072334454405 2414554509809638562710201)
            ·
              refine ⟨1810915882357228922032651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2414554509809638562710201 1810915882357228922032651)
              ·
                refine ⟨2716373823535843383048977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1810915882357228922032651 2716373823535843383048977)
                ·
                  refine ⟨2037280367651882537286733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2716373823535843383048977 2037280367651882537286733)
                  ·
                    refine ⟨763980137869455951482525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2037280367651882537286733 763980137869455951482525)
                    ·
                      rfl

theorem cell22_2231769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 2, 3].length) (baseStart_2231769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231769 prefixEnd_2231769 := by exact prefixLift 2231769
  have htrace : WordTrace (prefixWord ++ tailWord_2231769) baseStart_2231769 baseEnd_2231769 := by
    simpa [prefixWord, tailWord_2231769, baseEnd_2231769] using wordTrace_append hprefix tailTrace_2231769
  have hstable : (prefixWord ++ tailWord_2231769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231769).length < 2 ^ (prefixWord ++ tailWord_2231769).sum := by decide
  have hdescent : baseEnd_2231769 < baseStart_2231769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231780 : List Nat := [2, 3, 1, 1, 1, 1, 1, 6, 3, 3]
def baseStart_2231780 : Nat := 118140960795 + 2231780 * 2 ^ 59
def prefixEnd_2231780 : Nat := 4983230072969 + 3 ^ 40 * 2231780 * 2
def baseEnd_2231780 : Nat := 763983903394255589457491

theorem tailTrace_2231780 : CollatzResearch.WordTrace tailWord_2231780 prefixEnd_2231780 763983903394255589457491 := by
  unfold tailWord_2231780
  simp only [CollatzResearch.WordTrace]
  refine ⟨40699851927324846261798397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54266469236433128349064529 40699851927324846261798397)
  ·
    refine ⟨15262444472746817348174399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40699851927324846261798397 15262444472746817348174399)
    ·
      refine ⟨22893666709120226022261599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15262444472746817348174399 22893666709120226022261599)
      ·
        refine ⟨34340500063680339033392399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22893666709120226022261599 34340500063680339033392399)
        ·
          refine ⟨51510750095520508550088599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34340500063680339033392399 51510750095520508550088599)
          ·
            refine ⟨77266125143280762825132899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51510750095520508550088599 77266125143280762825132899)
            ·
              refine ⟨115899187714921144237699349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77266125143280762825132899 115899187714921144237699349)
              ·
                refine ⟨5432774424136928636142157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 115899187714921144237699349 5432774424136928636142157)
                ·
                  refine ⟨2037290409051348238553309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5432774424136928636142157 2037290409051348238553309)
                  ·
                    refine ⟨763983903394255589457491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2037290409051348238553309 763983903394255589457491)
                    ·
                      rfl

theorem cell22_2231780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_2231780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231780 prefixEnd_2231780 := by exact prefixLift 2231780
  have htrace : WordTrace (prefixWord ++ tailWord_2231780) baseStart_2231780 baseEnd_2231780 := by
    simpa [prefixWord, tailWord_2231780, baseEnd_2231780] using wordTrace_append hprefix tailTrace_2231780
  have hstable : (prefixWord ++ tailWord_2231780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231780).length < 2 ^ (prefixWord ++ tailWord_2231780).sum := by decide
  have hdescent : baseEnd_2231780 < baseStart_2231780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231883 : List Nat := [1, 1, 1, 1, 3, 1, 3, 11]
def baseStart_2231883 : Nat := 118140960795 + 2231883 * 2 ^ 59
def prefixEnd_2231883 : Nat := 4983230072969 + 3 ^ 40 * 2231883 * 2
def baseEnd_2231883 : Nat := 84891018044355294903575

theorem tailTrace_2231883 : CollatzResearch.WordTrace tailWord_2231883 prefixEnd_2231883 84891018044355294903575 := by
  unfold tailWord_2231883
  simp only [CollatzResearch.WordTrace]
  refine ⟨81403460573276541114596303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54268973715517694076397535 81403460573276541114596303)
  ·
    refine ⟨122105190859914811671894455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81403460573276541114596303 122105190859914811671894455)
    ·
      refine ⟨183157786289872217507841683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122105190859914811671894455 183157786289872217507841683)
      ·
        refine ⟨274736679434808326261762525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183157786289872217507841683 274736679434808326261762525)
        ·
          refine ⟨103026254788053122348160947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274736679434808326261762525 103026254788053122348160947)
          ·
            refine ⟨154539382182079683522241421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103026254788053122348160947 154539382182079683522241421)
            ·
              refine ⟨57952268318279881320840533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154539382182079683522241421 57952268318279881320840533)
              ·
                refine ⟨84891018044355294903575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 57952268318279881320840533 84891018044355294903575)
                ·
                  rfl

theorem cell22_2231883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 11].length) (baseStart_2231883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231883 prefixEnd_2231883 := by exact prefixLift 2231883
  have htrace : WordTrace (prefixWord ++ tailWord_2231883) baseStart_2231883 baseEnd_2231883 := by
    simpa [prefixWord, tailWord_2231883, baseEnd_2231883] using wordTrace_append hprefix tailTrace_2231883
  have hstable : (prefixWord ++ tailWord_2231883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231883).length < 2 ^ (prefixWord ++ tailWord_2231883).sum := by decide
  have hdescent : baseEnd_2231883 < baseStart_2231883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231917 : List Nat := [1, 5, 1, 1, 4, 2, 8]
def baseStart_2231917 : Nat := 118140960795 + 2231917 * 2 ^ 59
def prefixEnd_2231917 : Nat := 4983230072969 + 3 ^ 40 * 2231917 * 2
def baseEnd_2231917 : Nat := 28297437084964181436373

theorem tailTrace_2231917 : CollatzResearch.WordTrace tailWord_2231917 prefixEnd_2231917 28297437084964181436373 := by
  unfold tailWord_2231917
  simp only [CollatzResearch.WordTrace]
  refine ⟨81404700655153364921334005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54269800436768909947556003 81404700655153364921334005)
  ·
    refine ⟨7631690686420627961375063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81404700655153364921334005 7631690686420627961375063)
    ·
      refine ⟨11447536029630941942062595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7631690686420627961375063 11447536029630941942062595)
      ·
        refine ⟨17171304044446412913093893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11447536029630941942062595 17171304044446412913093893)
        ·
          refine ⟨3219619508333702421205105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17171304044446412913093893 3219619508333702421205105)
          ·
            refine ⟨2414714631250276815903829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3219619508333702421205105 2414714631250276815903829)
            ·
              refine ⟨28297437084964181436373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2414714631250276815903829 28297437084964181436373)
              ·
                rfl

theorem cell22_2231917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 8].length) (baseStart_2231917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231917 prefixEnd_2231917 := by exact prefixLift 2231917
  have htrace : WordTrace (prefixWord ++ tailWord_2231917) baseStart_2231917 baseEnd_2231917 := by
    simpa [prefixWord, tailWord_2231917, baseEnd_2231917] using wordTrace_append hprefix tailTrace_2231917
  have hstable : (prefixWord ++ tailWord_2231917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231917).length < 2 ^ (prefixWord ++ tailWord_2231917).sum := by decide
  have hdescent : baseEnd_2231917 < baseStart_2231917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232005 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 5, 5]
def baseStart_2232005 : Nat := 118140960795 + 2232005 * 2 ^ 59
def prefixEnd_2232005 : Nat := 4983230072969 + 3 ^ 40 * 2232005 * 2
def baseEnd_2232005 : Nat := 764060925492430002581801

theorem tailTrace_2232005 : CollatzResearch.WordTrace tailWord_2232005 prefixEnd_2232005 764060925492430002581801 := by
  unfold tailWord_2232005
  simp only [CollatzResearch.WordTrace]
  refine ⟨81407910278834555950537469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54271940185889703967024979 81407910278834555950537469)
  ·
    refine ⟨30527966354562958481451551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81407910278834555950537469 30527966354562958481451551)
    ·
      refine ⟨45791949531844437722177327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30527966354562958481451551 45791949531844437722177327)
      ·
        refine ⟨68687924297766656583265991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45791949531844437722177327 68687924297766656583265991)
        ·
          refine ⟨103031886446649984874898987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68687924297766656583265991 103031886446649984874898987)
          ·
            refine ⟨154547829669974977312348481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103031886446649984874898987 154547829669974977312348481)
            ·
              refine ⟨115910872252481232984261361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154547829669974977312348481 115910872252481232984261361)
              ·
                refine ⟨86933154189360924738196021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115910872252481232984261361 86933154189360924738196021)
                ·
                  refine ⟨8149983205252586694205877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86933154189360924738196021 8149983205252586694205877)
                  ·
                    refine ⟨764060925492430002581801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8149983205252586694205877 764060925492430002581801)
                    ·
                      rfl

theorem cell22_2232005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_2232005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232005 prefixEnd_2232005 := by exact prefixLift 2232005
  have htrace : WordTrace (prefixWord ++ tailWord_2232005) baseStart_2232005 baseEnd_2232005 := by
    simpa [prefixWord, tailWord_2232005, baseEnd_2232005] using wordTrace_append hprefix tailTrace_2232005
  have hstable : (prefixWord ++ tailWord_2232005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232005).length < 2 ^ (prefixWord ++ tailWord_2232005).sum := by decide
  have hdescent : baseEnd_2232005 < baseStart_2232005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232024 : List Nat := [2, 1, 2, 2, 3, 1, 4, 3, 4]
def baseStart_2232024 : Nat := 118140960795 + 2232024 * 2 ^ 59
def prefixEnd_2232024 : Nat := 4983230072969 + 3 ^ 40 * 2232024 * 2
def baseEnd_2232024 : Nat := 254689143193573428785581

theorem tailTrace_2232024 : CollatzResearch.WordTrace tailWord_2232024 prefixEnd_2232024 254689143193573428785581 := by
  unfold tailWord_2232024
  simp only [CollatzResearch.WordTrace]
  refine ⟨40704301632882861097739563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54272402177177148130319417 40704301632882861097739563)
  ·
    refine ⟨61056452449324291646609345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40704301632882861097739563 61056452449324291646609345)
    ·
      refine ⟨45792339336993218734957009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61056452449324291646609345 45792339336993218734957009)
      ·
        refine ⟨34344254502744914051217757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45792339336993218734957009 34344254502744914051217757)
        ·
          refine ⟨12879095438529342769206659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34344254502744914051217757 12879095438529342769206659)
          ·
            refine ⟨19318643157794014153809989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12879095438529342769206659 19318643157794014153809989)
            ·
              refine ⟨3622245592086377653839373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19318643157794014153809989 3622245592086377653839373)
              ·
                refine ⟨1358342097032391620189765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3622245592086377653839373 1358342097032391620189765)
                ·
                  refine ⟨254689143193573428785581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1358342097032391620189765 254689143193573428785581)
                  ·
                    rfl

theorem cell22_2232024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 4].length) (baseStart_2232024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232024 prefixEnd_2232024 := by exact prefixLift 2232024
  have htrace : WordTrace (prefixWord ++ tailWord_2232024) baseStart_2232024 baseEnd_2232024 := by
    simpa [prefixWord, tailWord_2232024, baseEnd_2232024] using wordTrace_append hprefix tailTrace_2232024
  have hstable : (prefixWord ++ tailWord_2232024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232024).length < 2 ^ (prefixWord ++ tailWord_2232024).sum := by decide
  have hdescent : baseEnd_2232024 < baseStart_2232024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232026 : List Nat := [3, 1, 1, 2, 2, 5, 2, 1, 1, 4]
def baseStart_2232026 : Nat := 118140960795 + 2232026 * 2 ^ 59
def prefixEnd_2232026 : Nat := 4983230072969 + 3 ^ 40 * 2232026 * 2
def baseEnd_2232026 : Nat := 764068114221592947806737

theorem tailTrace_2232026 : CollatzResearch.WordTrace tailWord_2232026 prefixEnd_2232026 764068114221592947806737 := by
  unfold tailWord_2232026
  simp only [CollatzResearch.WordTrace]
  refine ⟨20352169052939619134262983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54272450807838984358034621 20352169052939619134262983)
  ·
    refine ⟨30528253579409428701394475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20352169052939619134262983 30528253579409428701394475)
    ·
      refine ⟨45792380369114143052091713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30528253579409428701394475 45792380369114143052091713)
      ·
        refine ⟨34344285276835607289068785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45792380369114143052091713 34344285276835607289068785)
        ·
          refine ⟨25758213957626705466801589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34344285276835607289068785 25758213957626705466801589)
          ·
            refine ⟨2414832558527503637512649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25758213957626705466801589 2414832558527503637512649)
            ·
              refine ⟨1811124418895627728134487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2414832558527503637512649 1811124418895627728134487)
              ·
                refine ⟨2716686628343441592201731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1811124418895627728134487 2716686628343441592201731)
                ·
                  refine ⟨4075029942515162388302597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2716686628343441592201731 4075029942515162388302597)
                  ·
                    refine ⟨764068114221592947806737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4075029942515162388302597 764068114221592947806737)
                    ·
                      rfl

theorem cell22_2232026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 1, 4].length) (baseStart_2232026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232026 prefixEnd_2232026 := by exact prefixLift 2232026
  have htrace : WordTrace (prefixWord ++ tailWord_2232026) baseStart_2232026 baseEnd_2232026 := by
    simpa [prefixWord, tailWord_2232026, baseEnd_2232026] using wordTrace_append hprefix tailTrace_2232026
  have hstable : (prefixWord ++ tailWord_2232026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232026).length < 2 ^ (prefixWord ++ tailWord_2232026).sum := by decide
  have hdescent : baseEnd_2232026 < baseStart_2232026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232037 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 4, 4]
def baseStart_2232037 : Nat := 118140960795 + 2232037 * 2 ^ 59
def prefixEnd_2232037 : Nat := 4983230072969 + 3 ^ 40 * 2232037 * 2
def baseEnd_2232037 : Nat := 764071879746392585781703

theorem tailTrace_2232037 : CollatzResearch.WordTrace tailWord_2232037 prefixEnd_2232037 764071879746392585781703 := by
  unfold tailWord_2232037
  simp only [CollatzResearch.WordTrace]
  refine ⟨81409077414718625415702365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54272718276479083610468243 81409077414718625415702365)
  ·
    refine ⟨30528404030519484530888387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81409077414718625415702365 30528404030519484530888387)
    ·
      refine ⟨45792606045779226796332581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30528404030519484530888387 45792606045779226796332581)
      ·
        refine ⟨8586113633583605024312359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45792606045779226796332581 8586113633583605024312359)
        ·
          refine ⟨12879170450375407536468539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8586113633583605024312359 12879170450375407536468539)
          ·
            refine ⟨19318755675563111304702809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12879170450375407536468539 19318755675563111304702809)
            ·
              refine ⟨14489066756672333478527107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19318755675563111304702809 14489066756672333478527107)
              ·
                refine ⟨21733600135008500217790661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14489066756672333478527107 21733600135008500217790661)
                ·
                  refine ⟨4075050025314093790835749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21733600135008500217790661 4075050025314093790835749)
                  ·
                    refine ⟨764071879746392585781703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4075050025314093790835749 764071879746392585781703)
                    ·
                      rfl

theorem cell22_2232037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_2232037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232037 prefixEnd_2232037 := by exact prefixLift 2232037
  have htrace : WordTrace (prefixWord ++ tailWord_2232037) baseStart_2232037 baseEnd_2232037 := by
    simpa [prefixWord, tailWord_2232037, baseEnd_2232037] using wordTrace_append hprefix tailTrace_2232037
  have hstable : (prefixWord ++ tailWord_2232037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232037).length < 2 ^ (prefixWord ++ tailWord_2232037).sum := by decide
  have hdescent : baseEnd_2232037 < baseStart_2232037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232097 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 7]
def baseStart_2232097 : Nat := 118140960795 + 2232097 * 2 ^ 59
def prefixEnd_2232097 : Nat := 4983230072969 + 3 ^ 40 * 2232097 * 2
def baseEnd_2232097 : Nat := 254697472990857476427173

theorem tailTrace_2232097 : CollatzResearch.WordTrace tailWord_2232097 prefixEnd_2232097 254697472990857476427173 := by
  unfold tailWord_2232097
  simp only [CollatzResearch.WordTrace]
  refine ⟨81411265794501255662886545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54274177196334170441924363 81411265794501255662886545)
  ·
    refine ⟨61058449345875941747164909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81411265794501255662886545 61058449345875941747164909)
    ·
      refine ⟨22896918504703478155186841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61058449345875941747164909 22896918504703478155186841)
      ·
        refine ⟨17172688878527608616390131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22896918504703478155186841 17172688878527608616390131)
        ·
          refine ⟨25759033317791412924585197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17172688878527608616390131 25759033317791412924585197)
          ·
            refine ⟨9659637494171779846719449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25759033317791412924585197 9659637494171779846719449)
            ·
              refine ⟨7244728120628834885039587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9659637494171779846719449 7244728120628834885039587)
              ·
                refine ⟨10867092180943252327559381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7244728120628834885039587 10867092180943252327559381)
                ·
                  refine ⟨254697472990857476427173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10867092180943252327559381 254697472990857476427173)
                  ·
                    rfl

theorem cell22_2232097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 7].length) (baseStart_2232097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232097 prefixEnd_2232097 := by exact prefixLift 2232097
  have htrace : WordTrace (prefixWord ++ tailWord_2232097) baseStart_2232097 baseEnd_2232097 := by
    simpa [prefixWord, tailWord_2232097, baseEnd_2232097] using wordTrace_append hprefix tailTrace_2232097
  have hstable : (prefixWord ++ tailWord_2232097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232097).length < 2 ^ (prefixWord ++ tailWord_2232097).sum := by decide
  have hdescent : baseEnd_2232097 < baseStart_2232097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232101 : List Nat := [1, 3, 1, 2, 3, 4, 1, 1, 3, 3]
def baseStart_2232101 : Nat := 118140960795 + 2232101 * 2 ^ 59
def prefixEnd_2232101 : Nat := 4983230072969 + 3 ^ 40 * 2232101 * 2
def baseEnd_2232101 : Nat := 764093788254317752181507

theorem tailTrace_2232101 : CollatzResearch.WordTrace tailWord_2232101 prefixEnd_2232101 764093788254317752181507 := by
  unfold tailWord_2232101
  simp only [CollatzResearch.WordTrace]
  refine ⟨81411411686486764346032157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54274274457657842897354771 81411411686486764346032157)
  ·
    refine ⟨30529279382432536629762059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81411411686486764346032157 30529279382432536629762059)
    ·
      refine ⟨45793919073648804944643089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30529279382432536629762059 45793919073648804944643089)
      ·
        refine ⟨34345439305236603708482317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45793919073648804944643089 34345439305236603708482317)
        ·
          refine ⟨12879539739463726390680869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34345439305236603708482317 12879539739463726390680869)
          ·
            refine ⟨2414913701149448698252663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12879539739463726390680869 2414913701149448698252663)
            ·
              refine ⟨3622370551724173047378995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2414913701149448698252663 3622370551724173047378995)
              ·
                refine ⟨5433555827586259571068493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3622370551724173047378995 5433555827586259571068493)
                ·
                  refine ⟨2037583435344847339150685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5433555827586259571068493 2037583435344847339150685)
                  ·
                    refine ⟨764093788254317752181507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2037583435344847339150685 764093788254317752181507)
                    ·
                      rfl

theorem cell22_2232101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_2232101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232101 prefixEnd_2232101 := by exact prefixLift 2232101
  have htrace : WordTrace (prefixWord ++ tailWord_2232101) baseStart_2232101 baseEnd_2232101 := by
    simpa [prefixWord, tailWord_2232101, baseEnd_2232101] using wordTrace_append hprefix tailTrace_2232101
  have hstable : (prefixWord ++ tailWord_2232101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232101).length < 2 ^ (prefixWord ++ tailWord_2232101).sum := by decide
  have hdescent : baseEnd_2232101 < baseStart_2232101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232114 : List Nat := [3, 2, 1, 1, 3, 3, 1, 3, 5]
def baseStart_2232114 : Nat := 118140960795 + 2232114 * 2 ^ 59
def prefixEnd_2232114 : Nat := 4983230072969 + 3 ^ 40 * 2232114 * 2
def baseEnd_2232114 : Nat := 254699412806663350535489

theorem tailTrace_2232114 : CollatzResearch.WordTrace tailWord_2232114 prefixEnd_2232114 254699412806663350535489 := by
  unfold tailWord_2232114
  simp only [CollatzResearch.WordTrace]
  refine ⟨20352971458859916891563849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54274590556959778377503597 20352971458859916891563849)
  ·
    refine ⟨15264728594144937668672887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20352971458859916891563849 15264728594144937668672887)
    ·
      refine ⟨22897092891217406503009331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15264728594144937668672887 22897092891217406503009331)
      ·
        refine ⟨34345639336826109754513997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22897092891217406503009331 34345639336826109754513997)
        ·
          refine ⟨12879614751309791157942749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34345639336826109754513997 12879614751309791157942749)
          ·
            refine ⟨4829855531741171684228531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12879614751309791157942749 4829855531741171684228531)
            ·
              refine ⟨7244783297611757526342797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4829855531741171684228531 7244783297611757526342797)
              ·
                refine ⟨2716793736604409072378549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7244783297611757526342797 2716793736604409072378549)
                ·
                  refine ⟨254699412806663350535489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2716793736604409072378549 254699412806663350535489)
                  ·
                    rfl

theorem cell22_2232114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_2232114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232114 prefixEnd_2232114 := by exact prefixLift 2232114
  have htrace : WordTrace (prefixWord ++ tailWord_2232114) baseStart_2232114 baseEnd_2232114 := by
    simpa [prefixWord, tailWord_2232114, baseEnd_2232114] using wordTrace_append hprefix tailTrace_2232114
  have hstable : (prefixWord ++ tailWord_2232114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232114).length < 2 ^ (prefixWord ++ tailWord_2232114).sum := by decide
  have hdescent : baseEnd_2232114 < baseStart_2232114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232217 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 1, 8]
def baseStart_2232217 : Nat := 118140960795 + 2232217 * 2 ^ 59
def prefixEnd_2232217 : Nat := 4983230072969 + 3 ^ 40 * 2232217 * 2
def baseEnd_2232217 : Nat := 764133497424932116281151

theorem tailTrace_2232217 : CollatzResearch.WordTrace tailWord_2232217 prefixEnd_2232217 764133497424932116281151 := by
  unfold tailWord_2232217
  simp only [CollatzResearch.WordTrace]
  refine ⟨81415642554066516157254905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54277095036044344104836603 81415642554066516157254905)
  ·
    refine ⟨61061731915549887117941179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81415642554066516157254905 61061731915549887117941179)
    ·
      refine ⟨91592597873324830676911769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61061731915549887117941179 91592597873324830676911769)
      ·
        refine ⟨68694448404993623007683827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91592597873324830676911769 68694448404993623007683827)
        ·
          refine ⟨103041672607490434511525741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68694448404993623007683827 103041672607490434511525741)
          ·
            refine ⟨38640627227808912941822153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103041672607490434511525741 38640627227808912941822153)
            ·
              refine ⟨28980470420856684706366615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38640627227808912941822153 28980470420856684706366615)
              ·
                refine ⟨43470705631285027059549923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28980470420856684706366615 43470705631285027059549923)
                ·
                  refine ⟨65206058446927540589324885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43470705631285027059549923 65206058446927540589324885)
                  ·
                    refine ⟨764133497424932116281151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65206058446927540589324885 764133497424932116281151)
                    ·
                      rfl

theorem cell22_2232217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_2232217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232217 prefixEnd_2232217 := by exact prefixLift 2232217
  have htrace : WordTrace (prefixWord ++ tailWord_2232217) baseStart_2232217 baseEnd_2232217 := by
    simpa [prefixWord, tailWord_2232217, baseEnd_2232217] using wordTrace_append hprefix tailTrace_2232217
  have hstable : (prefixWord ++ tailWord_2232217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232217).length < 2 ^ (prefixWord ++ tailWord_2232217).sum := by decide
  have hdescent : baseEnd_2232217 < baseStart_2232217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232225 : List Nat := [1, 2, 3, 4, 2, 1, 3, 1, 2, 3]
def baseStart_2232225 : Nat := 118140960795 + 2232225 * 2 ^ 59
def prefixEnd_2232225 : Nat := 4983230072969 + 3 ^ 40 * 2232225 * 2
def baseEnd_2232225 : Nat := 764136235988422762081127

theorem tailTrace_2232225 : CollatzResearch.WordTrace tailWord_2232225 prefixEnd_2232225 764136235988422762081127 := by
  unfold tailWord_2232225
  simp only [CollatzResearch.WordTrace]
  refine ⟨81415934338037533523546129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54277289558691689015697419 81415934338037533523546129)
  ·
    refine ⟨61061950753528150142659597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81415934338037533523546129 61061950753528150142659597)
    ·
      refine ⟨22898231532573056303497349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61061950753528150142659597 22898231532573056303497349)
      ·
        refine ⟨4293418412357448056905753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22898231532573056303497349 4293418412357448056905753)
        ·
          refine ⟨3220063809268086042679315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4293418412357448056905753 3220063809268086042679315)
          ·
            refine ⟨4830095713902129064018973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3220063809268086042679315 4830095713902129064018973)
            ·
              refine ⟨1811285892713298399007115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4830095713902129064018973 1811285892713298399007115)
              ·
                refine ⟨2716928839069947598510673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1811285892713298399007115 2716928839069947598510673)
                ·
                  refine ⟨2037696629302460698883005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2716928839069947598510673 2037696629302460698883005)
                  ·
                    refine ⟨764136235988422762081127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2037696629302460698883005 764136235988422762081127)
                    ·
                      rfl

theorem cell22_2232225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_2232225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232225 prefixEnd_2232225 := by exact prefixLift 2232225
  have htrace : WordTrace (prefixWord ++ tailWord_2232225) baseStart_2232225 baseEnd_2232225 := by
    simpa [prefixWord, tailWord_2232225, baseEnd_2232225] using wordTrace_append hprefix tailTrace_2232225
  have hstable : (prefixWord ++ tailWord_2232225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232225).length < 2 ^ (prefixWord ++ tailWord_2232225).sum := by decide
  have hdescent : baseEnd_2232225 < baseStart_2232225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232270 : List Nat := [4, 1, 1, 1, 2, 2, 5, 2, 1, 3]
def baseStart_2232270 : Nat := 118140960795 + 2232270 * 2 ^ 59
def prefixEnd_2232270 : Nat := 4983230072969 + 3 ^ 40 * 2232270 * 2
def baseEnd_2232270 : Nat := 764151640408057644705989

theorem tailTrace_2232270 : CollatzResearch.WordTrace tailWord_2232270 prefixEnd_2232270 764151640408057644705989 := by
  unfold tailWord_2232270
  simp only [CollatzResearch.WordTrace]
  refine ⟨10177196952859313276116783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54278383748583004139289509 10177196952859313276116783)
  ·
    refine ⟨15265795429288969914175175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10177196952859313276116783 15265795429288969914175175)
    ·
      refine ⟨22898693143933454871262763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15265795429288969914175175 22898693143933454871262763)
      ·
        refine ⟨34348039715900182306894145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22898693143933454871262763 34348039715900182306894145)
        ·
          refine ⟨25761029786925136730170609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34348039715900182306894145 25761029786925136730170609)
          ·
            refine ⟨19320772340193852547627957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25761029786925136730170609 19320772340193852547627957)
            ·
              refine ⟨1811322406893173676340121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19320772340193852547627957 1811322406893173676340121)
              ·
                refine ⟨1358491805169880257255091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1811322406893173676340121 1358491805169880257255091)
                ·
                  refine ⟨2037737707754820385882637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1358491805169880257255091 2037737707754820385882637)
                  ·
                    refine ⟨764151640408057644705989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2037737707754820385882637 764151640408057644705989)
                    ·
                      rfl

theorem cell22_2232270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_2232270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232270 prefixEnd_2232270 := by exact prefixLift 2232270
  have htrace : WordTrace (prefixWord ++ tailWord_2232270) baseStart_2232270 baseEnd_2232270 := by
    simpa [prefixWord, tailWord_2232270, baseEnd_2232270] using wordTrace_append hprefix tailTrace_2232270
  have hstable : (prefixWord ++ tailWord_2232270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232270).length < 2 ^ (prefixWord ++ tailWord_2232270).sum := by decide
  have hdescent : baseEnd_2232270 < baseStart_2232270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232279 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 3, 4]
def baseStart_2232279 : Nat := 118140960795 + 2232279 * 2 ^ 59
def prefixEnd_2232279 : Nat := 4983230072969 + 3 ^ 40 * 2232279 * 2
def baseEnd_2232279 : Nat := 764154721291984621230961

theorem tailTrace_2232279 : CollatzResearch.WordTrace tailWord_2232279 prefixEnd_2232279 764154721291984621230961 := by
  unfold tailWord_2232279
  simp only [CollatzResearch.WordTrace]
  refine ⟨81417903879841900746011891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54278602586561267164007927 81417903879841900746011891)
  ·
    refine ⟨122126855819762851119017837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81417903879841900746011891 122126855819762851119017837)
    ·
      refine ⟨45797570932411069169631689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122126855819762851119017837 45797570932411069169631689)
      ·
        refine ⟨34348178199308301877223767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45797570932411069169631689 34348178199308301877223767)
        ·
          refine ⟨51522267298962452815835651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34348178199308301877223767 51522267298962452815835651)
          ·
            refine ⟨77283400948443679223753477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51522267298962452815835651 77283400948443679223753477)
            ·
              refine ⟨14490637677833189854453777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77283400948443679223753477 14490637677833189854453777)
              ·
                refine ⟨10867978258374892390840333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14490637677833189854453777 10867978258374892390840333)
                ·
                  refine ⟨4075491846890584646565125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10867978258374892390840333 4075491846890584646565125)
                  ·
                    refine ⟨764154721291984621230961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4075491846890584646565125 764154721291984621230961)
                    ·
                      rfl

theorem cell22_2232279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_2232279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232279 prefixEnd_2232279 := by exact prefixLift 2232279
  have htrace : WordTrace (prefixWord ++ tailWord_2232279) baseStart_2232279 baseEnd_2232279 := by
    simpa [prefixWord, tailWord_2232279, baseEnd_2232279] using wordTrace_append hprefix tailTrace_2232279
  have hstable : (prefixWord ++ tailWord_2232279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232279).length < 2 ^ (prefixWord ++ tailWord_2232279).sum := by decide
  have hdescent : baseEnd_2232279 < baseStart_2232279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232313 : List Nat := [1, 2, 1, 3, 1, 5, 3, 1, 1, 4]
def baseStart_2232313 : Nat := 118140960795 + 2232313 * 2 ^ 59
def prefixEnd_2232313 : Nat := 4983230072969 + 3 ^ 40 * 2232313 * 2
def baseEnd_2232313 : Nat := 764166360186819865880857

theorem tailTrace_2232313 : CollatzResearch.WordTrace tailWord_2232313 prefixEnd_2232313 764166360186819865880857 := by
  unfold tailWord_2232313
  simp only [CollatzResearch.WordTrace]
  refine ⟨81419143961718724552749593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54279429307812483035166395 81419143961718724552749593)
  ·
    refine ⟨61064357971289043414562195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81419143961718724552749593 61064357971289043414562195)
    ·
      refine ⟨91596536956933565121843293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61064357971289043414562195 91596536956933565121843293)
      ·
        refine ⟨34348701358850086920691235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91596536956933565121843293 34348701358850086920691235)
        ·
          refine ⟨51523052038275130381036853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34348701358850086920691235 51523052038275130381036853)
          ·
            refine ⟨4830286128588293473222205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51523052038275130381036853 4830286128588293473222205)
            ·
              refine ⟨1811357298220610052458327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4830286128588293473222205 1811357298220610052458327)
              ·
                refine ⟨2717035947330915078687491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1811357298220610052458327 2717035947330915078687491)
                ·
                  refine ⟨4075553920996372618031237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2717035947330915078687491 4075553920996372618031237)
                  ·
                    refine ⟨764166360186819865880857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4075553920996372618031237 764166360186819865880857)
                    ·
                      rfl

theorem cell22_2232313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 1, 4].length) (baseStart_2232313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232313 prefixEnd_2232313 := by exact prefixLift 2232313
  have htrace : WordTrace (prefixWord ++ tailWord_2232313) baseStart_2232313 baseEnd_2232313 := by
    simpa [prefixWord, tailWord_2232313, baseEnd_2232313] using wordTrace_append hprefix tailTrace_2232313
  have hstable : (prefixWord ++ tailWord_2232313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232313).length < 2 ^ (prefixWord ++ tailWord_2232313).sum := by decide
  have hdescent : baseEnd_2232313 < baseStart_2232313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232339 : List Nat := [1, 1, 1, 2, 1, 4, 5, 7]
def baseStart_2232339 : Nat := 118140960795 + 2232339 * 2 ^ 59
def prefixEnd_2232339 : Nat := 4983230072969 + 3 ^ 40 * 2232339 * 2
def baseEnd_2232339 : Nat := 84908362279796051636753

theorem tailTrace_2232339 : CollatzResearch.WordTrace tailWord_2232339 prefixEnd_2232339 84908362279796051636753 := by
  unfold tailWord_2232339
  simp only [CollatzResearch.WordTrace]
  refine ⟨81420092259624530993196071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54280061506416353995464047 81420092259624530993196071)
  ·
    refine ⟨122130138389436796489794107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81420092259624530993196071 122130138389436796489794107)
    ·
      refine ⟨183195207584155194734691161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122130138389436796489794107 183195207584155194734691161)
      ·
        refine ⟨137396405688116396051018371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183195207584155194734691161 137396405688116396051018371)
        ·
          refine ⟨206094608532174594076527557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137396405688116396051018371 206094608532174594076527557)
          ·
            refine ⟨38642739099782736389348917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206094608532174594076527557 38642739099782736389348917)
            ·
              refine ⟨3622756790604631536501461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38642739099782736389348917 3622756790604631536501461)
              ·
                refine ⟨84908362279796051636753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3622756790604631536501461 84908362279796051636753)
                ·
                  rfl

theorem cell22_2232339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 7].length) (baseStart_2232339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232339 prefixEnd_2232339 := by exact prefixLift 2232339
  have htrace : WordTrace (prefixWord ++ tailWord_2232339) baseStart_2232339 baseEnd_2232339 := by
    simpa [prefixWord, tailWord_2232339, baseEnd_2232339] using wordTrace_append hprefix tailTrace_2232339
  have hstable : (prefixWord ++ tailWord_2232339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232339).length < 2 ^ (prefixWord ++ tailWord_2232339).sum := by decide
  have hdescent : baseEnd_2232339 < baseStart_2232339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232343 : List Nat := [1, 1, 3, 5, 2, 1, 2, 1, 1, 5]
def baseStart_2232343 : Nat := 118140960795 + 2232343 * 2 ^ 59
def prefixEnd_2232343 : Nat := 4983230072969 + 3 ^ 40 * 2232343 * 2
def baseEnd_2232343 : Nat := 764176629799909787630765

theorem tailTrace_2232343 : CollatzResearch.WordTrace tailWord_2232343 prefixEnd_2232343 764176629799909787630765 := by
  unfold tailWord_2232343
  simp only [CollatzResearch.WordTrace]
  refine ⟨81420238151610039676341683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54280158767740026450894455 81420238151610039676341683)
  ·
    refine ⟨122130357227415059514512525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81420238151610039676341683 122130357227415059514512525)
    ·
      refine ⟨45798883960280647317942197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122130357227415059514512525 45798883960280647317942197)
      ·
        refine ⟨4293645371276310686057081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45798883960280647317942197 4293645371276310686057081)
        ·
          refine ⟨3220234028457233014542811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4293645371276310686057081 3220234028457233014542811)
          ·
            refine ⟨4830351042685849521814217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3220234028457233014542811 4830351042685849521814217)
            ·
              refine ⟨3622763282014387141360663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4830351042685849521814217 3622763282014387141360663)
              ·
                refine ⟨5434144923021580712040995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3622763282014387141360663 5434144923021580712040995)
                ·
                  refine ⟨8151217384532371068061493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5434144923021580712040995 8151217384532371068061493)
                  ·
                    refine ⟨764176629799909787630765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8151217384532371068061493 764176629799909787630765)
                    ·
                      rfl

theorem cell22_2232343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_2232343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232343 prefixEnd_2232343 := by exact prefixLift 2232343
  have htrace : WordTrace (prefixWord ++ tailWord_2232343) baseStart_2232343 baseEnd_2232343 := by
    simpa [prefixWord, tailWord_2232343, baseEnd_2232343] using wordTrace_append hprefix tailTrace_2232343
  have hstable : (prefixWord ++ tailWord_2232343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232343).length < 2 ^ (prefixWord ++ tailWord_2232343).sum := by decide
  have hdescent : baseEnd_2232343 < baseStart_2232343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232377 : List Nat := [1, 2, 1, 5, 4, 1, 1, 2, 2, 3]
def baseStart_2232377 : Nat := 118140960795 + 2232377 * 2 ^ 59
def prefixEnd_2232377 : Nat := 4983230072969 + 3 ^ 40 * 2232377 * 2
def baseEnd_2232377 : Nat := 764188268694745032280661

theorem tailTrace_2232377 : CollatzResearch.WordTrace tailWord_2232377 prefixEnd_2232377 764188268694745032280661 := by
  unfold tailWord_2232377
  simp only [CollatzResearch.WordTrace]
  refine ⟨81421478233486863483079385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54280985488991242322052923 81421478233486863483079385)
  ·
    refine ⟨61066108675115147612309539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81421478233486863483079385 61066108675115147612309539)
    ·
      refine ⟨91599163012672721418464309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61066108675115147612309539 91599163012672721418464309)
      ·
        refine ⟨8587421532438067632981029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91599163012672721418464309 8587421532438067632981029)
        ·
          refine ⟨1610141537332137681183943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8587421532438067632981029 1610141537332137681183943)
          ·
            refine ⟨2415212305998206521775915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1610141537332137681183943 2415212305998206521775915)
            ·
              refine ⟨3622818458997309782663873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2415212305998206521775915 3622818458997309782663873)
              ·
                refine ⟨2717113844247982336997905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3622818458997309782663873 2717113844247982336997905)
                ·
                  refine ⟨2037835383185986752748429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2717113844247982336997905 2037835383185986752748429)
                  ·
                    refine ⟨764188268694745032280661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2037835383185986752748429 764188268694745032280661)
                    ·
                      rfl

theorem cell22_2232377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 2, 3].length) (baseStart_2232377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232377 prefixEnd_2232377 := by exact prefixLift 2232377
  have htrace : WordTrace (prefixWord ++ tailWord_2232377) baseStart_2232377 baseEnd_2232377 := by
    simpa [prefixWord, tailWord_2232377, baseEnd_2232377] using wordTrace_append hprefix tailTrace_2232377
  have hstable : (prefixWord ++ tailWord_2232377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232377).length < 2 ^ (prefixWord ++ tailWord_2232377).sum := by decide
  have hdescent : baseEnd_2232377 < baseStart_2232377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232482 : List Nat := [3, 3, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_2232482 : Nat := 118140960795 + 2232482 * 2 ^ 59
def prefixEnd_2232482 : Nat := 4983230072969 + 3 ^ 40 * 2232482 * 2
def baseEnd_2232482 : Nat := 764224212340559758405339

theorem tailTrace_2232482 : CollatzResearch.WordTrace tailWord_2232482 prefixEnd_2232482 764224212340559758405339 := by
  unfold tailWord_2232482
  simp only [CollatzResearch.WordTrace]
  refine ⟨20356326974526616603912925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54283538598737644277101133 20356326974526616603912925)
  ·
    refine ⟨7633622615447481226467347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20356326974526616603912925 7633622615447481226467347)
    ·
      refine ⟨11450433923171221839701021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7633622615447481226467347 11450433923171221839701021)
      ·
        refine ⟨4293912721189208189887883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11450433923171221839701021 4293912721189208189887883)
        ·
          refine ⟨6440869081783812284831825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4293912721189208189887883 6440869081783812284831825)
          ·
            refine ⟨4830651811337859213623869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6440869081783812284831825 4830651811337859213623869)
            ·
              refine ⟨1811494429251697205108951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4830651811337859213623869 1811494429251697205108951)
              ·
                refine ⟨2717241643877545807663427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1811494429251697205108951 2717241643877545807663427)
                ·
                  refine ⟨4075862465816318711495141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2717241643877545807663427 4075862465816318711495141)
                  ·
                    refine ⟨764224212340559758405339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4075862465816318711495141 764224212340559758405339)
                    ·
                      rfl

theorem cell22_2232482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_2232482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232482 prefixEnd_2232482 := by exact prefixLift 2232482
  have htrace : WordTrace (prefixWord ++ tailWord_2232482) baseStart_2232482 baseEnd_2232482 := by
    simpa [prefixWord, tailWord_2232482, baseEnd_2232482] using wordTrace_append hprefix tailTrace_2232482
  have hstable : (prefixWord ++ tailWord_2232482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232482).length < 2 ^ (prefixWord ++ tailWord_2232482).sum := by decide
  have hdescent : baseEnd_2232482 < baseStart_2232482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232523 : List Nat := [1, 1, 1, 1, 3, 2, 5, 2, 3, 3]
def baseStart_2232523 : Nat := 118140960795 + 2232523 * 2 ^ 59
def prefixEnd_2232523 : Nat := 4983230072969 + 3 ^ 40 * 2232523 * 2
def baseEnd_2232523 : Nat := 764238247478449318130213

theorem tailTrace_2232523 : CollatzResearch.WordTrace tailWord_2232523 prefixEnd_2232523 764238247478449318130213 := by
  unfold tailWord_2232523
  simp only [CollatzResearch.WordTrace]
  refine ⟨81426803290957930417894223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54284535527305286945262815 81426803290957930417894223)
  ·
    refine ⟨122140204936436895626841335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81426803290957930417894223 122140204936436895626841335)
    ·
      refine ⟨183210307404655343440262003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122140204936436895626841335 183210307404655343440262003)
      ·
        refine ⟨274815461106983015160393005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183210307404655343440262003 274815461106983015160393005)
        ·
          refine ⟨103055797915118630685147377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274815461106983015160393005 103055797915118630685147377)
          ·
            refine ⟨77291848436338973013860533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103055797915118630685147377 77291848436338973013860533)
            ·
              refine ⟨7246110790906778720049425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77291848436338973013860533 7246110790906778720049425)
              ·
                refine ⟨5434583093180084040037069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7246110790906778720049425 5434583093180084040037069)
                ·
                  refine ⟨2037968659942531515013901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5434583093180084040037069 2037968659942531515013901)
                  ·
                    refine ⟨764238247478449318130213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2037968659942531515013901 764238247478449318130213)
                    ·
                      rfl

theorem cell22_2232523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 3].length) (baseStart_2232523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232523 prefixEnd_2232523 := by exact prefixLift 2232523
  have htrace : WordTrace (prefixWord ++ tailWord_2232523) baseStart_2232523 baseEnd_2232523 := by
    simpa [prefixWord, tailWord_2232523, baseEnd_2232523] using wordTrace_append hprefix tailTrace_2232523
  have hstable : (prefixWord ++ tailWord_2232523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232523).length < 2 ^ (prefixWord ++ tailWord_2232523).sum := by decide
  have hdescent : baseEnd_2232523 < baseStart_2232523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232557 : List Nat := [1, 5, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_2232557 : Nat := 118140960795 + 2232557 * 2 ^ 59
def prefixEnd_2232557 : Nat := 4983230072969 + 3 ^ 40 * 2232557 * 2
def baseEnd_2232557 : Nat := 764249886373284562780109

theorem tailTrace_2232557 : CollatzResearch.WordTrace tailWord_2232557 prefixEnd_2232557 764249886373284562780109 := by
  unfold tailWord_2232557
  simp only [CollatzResearch.WordTrace]
  refine ⟨81428043372834754224631925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54285362248556502816421283 81428043372834754224631925)
  ·
    refine ⟨7633879066203258208559243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81428043372834754224631925 7633879066203258208559243)
    ·
      refine ⟨11450818599304887312838865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7633879066203258208559243 11450818599304887312838865)
      ·
        refine ⟨8588113949478665484629149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11450818599304887312838865 8588113949478665484629149)
        ·
          refine ⟨3220542731054499556735931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8588113949478665484629149 3220542731054499556735931)
          ·
            refine ⟨4830814096581749335103897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3220542731054499556735931 4830814096581749335103897)
            ·
              refine ⟨3623110572436312001327923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4830814096581749335103897 3623110572436312001327923)
              ·
                refine ⟨5434665858654468001991885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3623110572436312001327923 5434665858654468001991885)
                ·
                  refine ⟨2037999696995425500746957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5434665858654468001991885 2037999696995425500746957)
                  ·
                    refine ⟨764249886373284562780109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2037999696995425500746957 764249886373284562780109)
                    ·
                      rfl

theorem cell22_2232557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_2232557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232557 prefixEnd_2232557 := by exact prefixLift 2232557
  have htrace : WordTrace (prefixWord ++ tailWord_2232557) baseStart_2232557 baseEnd_2232557 := by
    simpa [prefixWord, tailWord_2232557, baseEnd_2232557] using wordTrace_append hprefix tailTrace_2232557
  have hstable : (prefixWord ++ tailWord_2232557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232557).length < 2 ^ (prefixWord ++ tailWord_2232557).sum := by decide
  have hdescent : baseEnd_2232557 < baseStart_2232557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232570 : List Nat := [3, 1, 1, 1, 1, 6, 3, 1, 5]
def baseStart_2232570 : Nat := 118140960795 + 2232570 * 2 ^ 59
def prefixEnd_2232570 : Nat := 4983230072969 + 3 ^ 40 * 2232570 * 2
def baseEnd_2232570 : Nat := 254751445512985620735023

theorem tailTrace_2232570 : CollatzResearch.WordTrace tailWord_2232570 prefixEnd_2232570 254751445512985620735023 := by
  unfold tailWord_2232570
  simp only [CollatzResearch.WordTrace]
  refine ⟨20357129380446914361213791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54285678347858438296570109 20357129380446914361213791)
  ·
    refine ⟨30535694070670371541820687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20357129380446914361213791 30535694070670371541820687)
    ·
      refine ⟨45803541106005557312731031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30535694070670371541820687 45803541106005557312731031)
      ·
        refine ⟨68705311659008335969096547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45803541106005557312731031 68705311659008335969096547)
        ·
          refine ⟨103057967488512503953644821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68705311659008335969096547 103057967488512503953644821)
          ·
            refine ⟨4830842226024023622827101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103057967488512503953644821 4830842226024023622827101)
            ·
              refine ⟨1811565834759008858560163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4830842226024023622827101 1811565834759008858560163)
              ·
                refine ⟨2717348752138513287840245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1811565834759008858560163 2717348752138513287840245)
                ·
                  refine ⟨254751445512985620735023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2717348752138513287840245 254751445512985620735023)
                  ·
                    rfl

theorem cell22_2232570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_2232570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232570 prefixEnd_2232570 := by exact prefixLift 2232570
  have htrace : WordTrace (prefixWord ++ tailWord_2232570) baseStart_2232570 baseEnd_2232570 := by
    simpa [prefixWord, tailWord_2232570, baseEnd_2232570] using wordTrace_append hprefix tailTrace_2232570
  have hstable : (prefixWord ++ tailWord_2232570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232570).length < 2 ^ (prefixWord ++ tailWord_2232570).sum := by decide
  have hdescent : baseEnd_2232570 < baseStart_2232570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232581 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 8]
def baseStart_2232581 : Nat := 118140960795 + 2232581 * 2 ^ 59
def prefixEnd_2232581 : Nat := 4983230072969 + 3 ^ 40 * 2232581 * 2
def baseEnd_2232581 : Nat := 254752700687918833393345

theorem tailTrace_2232581 : CollatzResearch.WordTrace tailWord_2232581 prefixEnd_2232581 254752700687918833393345 := by
  unfold tailWord_2232581
  simp only [CollatzResearch.WordTrace]
  refine ⟨81428918724747806323505597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54285945816498537549003731 81428918724747806323505597)
  ·
    refine ⟨30535844521780427371314599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81428918724747806323505597 30535844521780427371314599)
    ·
      refine ⟨45803766782670641056971899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30535844521780427371314599 45803766782670641056971899)
      ·
        refine ⟨68705650174005961585457849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45803766782670641056971899 68705650174005961585457849)
        ·
          refine ⟨51529237630504471189093387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68705650174005961585457849 51529237630504471189093387)
          ·
            refine ⟨77293856445756706783640081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51529237630504471189093387 77293856445756706783640081)
            ·
              refine ⟨57970392334317530087730061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77293856445756706783640081 57970392334317530087730061)
              ·
                refine ⟨21738897125369073782898773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57970392334317530087730061 21738897125369073782898773)
                ·
                  refine ⟨254752700687918833393345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21738897125369073782898773 254752700687918833393345)
                  ·
                    rfl

theorem cell22_2232581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_2232581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232581 prefixEnd_2232581 := by exact prefixLift 2232581
  have htrace : WordTrace (prefixWord ++ tailWord_2232581) baseStart_2232581 baseEnd_2232581 := by
    simpa [prefixWord, tailWord_2232581, baseEnd_2232581] using wordTrace_append hprefix tailTrace_2232581
  have hstable : (prefixWord ++ tailWord_2232581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232581).length < 2 ^ (prefixWord ++ tailWord_2232581).sum := by decide
  have hdescent : baseEnd_2232581 < baseStart_2232581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232621 : List Nat := [1, 5, 3, 1, 3, 1, 2, 1, 5]
def baseStart_2232621 : Nat := 118140960795 + 2232621 * 2 ^ 59
def prefixEnd_2232621 : Nat := 4983230072969 + 3 ^ 40 * 2232621 * 2
def baseEnd_2232621 : Nat := 254757264960403243059971

theorem tailTrace_2232621 : CollatzResearch.WordTrace tailWord_2232621 prefixEnd_2232621 254757264960403243059971 := by
  unfold tailWord_2232621
  simp only [CollatzResearch.WordTrace]
  refine ⟨81430377644602893154961717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54286918429735262103307811 81430377644602893154961717)
  ·
    refine ⟨7634097904181521233277661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81430377644602893154961717 7634097904181521233277661)
    ·
      refine ⟨2862786714068070462479123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7634097904181521233277661 2862786714068070462479123)
      ·
        refine ⟨4294180071102105693718685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2862786714068070462479123 4294180071102105693718685)
        ·
          refine ⟨1610317526663289635144507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4294180071102105693718685 1610317526663289635144507)
          ·
            refine ⟨2415476289994934452716761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1610317526663289635144507 2415476289994934452716761)
            ·
              refine ⟨1811607217496200839537571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2415476289994934452716761 1811607217496200839537571)
              ·
                refine ⟨2717410826244301259306357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1811607217496200839537571 2717410826244301259306357)
                ·
                  refine ⟨254757264960403243059971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2717410826244301259306357 254757264960403243059971)
                  ·
                    rfl

theorem cell22_2232621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_2232621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232621 prefixEnd_2232621 := by exact prefixLift 2232621
  have htrace : WordTrace (prefixWord ++ tailWord_2232621) baseStart_2232621 baseEnd_2232621 := by
    simpa [prefixWord, tailWord_2232621, baseEnd_2232621] using wordTrace_append hprefix tailTrace_2232621
  have hstable : (prefixWord ++ tailWord_2232621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232621).length < 2 ^ (prefixWord ++ tailWord_2232621).sum := by decide
  have hdescent : baseEnd_2232621 < baseStart_2232621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232675 : List Nat := [1, 1, 1, 5, 2, 1, 2, 3, 3, 3]
def baseStart_2232675 : Nat := 118140960795 + 2232675 * 2 ^ 59
def prefixEnd_2232675 : Nat := 4983230072969 + 3 ^ 40 * 2232675 * 2
def baseEnd_2232675 : Nat := 764290280184771588329747

theorem tailTrace_2232675 : CollatzResearch.WordTrace tailWord_2232675 prefixEnd_2232675 764290280184771588329747 := by
  unfold tailWord_2232675
  simp only [CollatzResearch.WordTrace]
  refine ⟨81432347186407260377427479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54288231457604840251618319 81432347186407260377427479)
  ·
    refine ⟨122148520779610890566141219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81432347186407260377427479 122148520779610890566141219)
    ·
      refine ⟨183222781169416335849211829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122148520779610890566141219 183222781169416335849211829)
      ·
        refine ⟨17177135734632781485863609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 183222781169416335849211829 17177135734632781485863609)
        ·
          refine ⟨12882851800974586114397707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17177135734632781485863609 12882851800974586114397707)
          ·
            refine ⟨19324277701461879171596561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12882851800974586114397707 19324277701461879171596561)
            ·
              refine ⟨14493208276096409378697421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19324277701461879171596561 14493208276096409378697421)
              ·
                refine ⟨5434953103536153517011533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14493208276096409378697421 5434953103536153517011533)
                ·
                  refine ⟨2038107413826057568879325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5434953103536153517011533 2038107413826057568879325)
                  ·
                    refine ⟨764290280184771588329747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2038107413826057568879325 764290280184771588329747)
                    ·
                      rfl

theorem cell22_2232675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 3].length) (baseStart_2232675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232675 prefixEnd_2232675 := by exact prefixLift 2232675
  have htrace : WordTrace (prefixWord ++ tailWord_2232675) baseStart_2232675 baseEnd_2232675 := by
    simpa [prefixWord, tailWord_2232675, baseEnd_2232675] using wordTrace_append hprefix tailTrace_2232675
  have hstable : (prefixWord ++ tailWord_2232675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232675).length < 2 ^ (prefixWord ++ tailWord_2232675).sum := by decide
  have hdescent : baseEnd_2232675 < baseStart_2232675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232694 : List Nat := [5, 1, 1, 4, 1, 1, 3, 6]
def baseStart_2232694 : Nat := 118140960795 + 2232694 * 2 ^ 59
def prefixEnd_2232694 : Nat := 4983230072969 + 3 ^ 40 * 2232694 * 2
def baseEnd_2232694 : Nat := 84921864919229096900521

theorem tailTrace_2232694 : CollatzResearch.WordTrace tailWord_2232694 prefixEnd_2232694 84921864919229096900521 := by
  unfold tailWord_2232694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5089565010833651663898071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54288693448892284414912757 5089565010833651663898071)
  ·
    refine ⟨7634347516250477495847107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5089565010833651663898071 7634347516250477495847107)
    ·
      refine ⟨11451521274375716243770661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7634347516250477495847107 11451521274375716243770661)
      ·
        refine ⟨2147160238945446795706999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11451521274375716243770661 2147160238945446795706999)
        ·
          refine ⟨3220740358418170193560499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2147160238945446795706999 3220740358418170193560499)
          ·
            refine ⟨4831110537627255290340749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3220740358418170193560499 4831110537627255290340749)
            ·
              refine ⟨1811666451610220733877781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4831110537627255290340749 1811666451610220733877781)
              ·
                refine ⟨84921864919229096900521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1811666451610220733877781 84921864919229096900521)
                ·
                  rfl

theorem cell22_2232694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_2232694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232694 prefixEnd_2232694 := by exact prefixLift 2232694
  have htrace : WordTrace (prefixWord ++ tailWord_2232694) baseStart_2232694 baseEnd_2232694 := by
    simpa [prefixWord, tailWord_2232694, baseEnd_2232694] using wordTrace_append hprefix tailTrace_2232694
  have hstable : (prefixWord ++ tailWord_2232694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232694).length < 2 ^ (prefixWord ++ tailWord_2232694).sum := by decide
  have hdescent : baseEnd_2232694 < baseStart_2232694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232782 : List Nat := [4, 1, 1, 1, 2, 1, 1, 6, 2, 3]
def baseStart_2232782 : Nat := 118140960795 + 2232782 * 2 ^ 59
def prefixEnd_2232782 : Nat := 4983230072969 + 3 ^ 40 * 2232782 * 2
def baseEnd_2232782 : Nat := 764326908471458975904419

theorem tailTrace_2232782 : CollatzResearch.WordTrace tailWord_2232782 prefixEnd_2232782 764326908471458975904419 := by
  unfold tailWord_2232782
  simp only [CollatzResearch.WordTrace]
  refine ⟨10179531224627452206446575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54290833198013078434381733 10179531224627452206446575)
  ·
    refine ⟨15269296836941178309669863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10179531224627452206446575 15269296836941178309669863)
    ·
      refine ⟨22903945255411767464504795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15269296836941178309669863 22903945255411767464504795)
      ·
        refine ⟨34355917883117651196757193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22903945255411767464504795 34355917883117651196757193)
        ·
          refine ⟨25766938412338238397567895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34355917883117651196757193 25766938412338238397567895)
          ·
            refine ⟨38650407618507357596351843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25766938412338238397567895 38650407618507357596351843)
            ·
              refine ⟨57975611427761036394527765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38650407618507357596351843 57975611427761036394527765)
              ·
                refine ⟨2717606785676298580993489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57975611427761036394527765 2717606785676298580993489)
                ·
                  refine ⟨2038205089257223935745117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2717606785676298580993489 2038205089257223935745117)
                  ·
                    refine ⟨764326908471458975904419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2038205089257223935745117 764326908471458975904419)
                    ·
                      rfl

theorem cell22_2232782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_2232782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232782 prefixEnd_2232782 := by exact prefixLift 2232782
  have htrace : WordTrace (prefixWord ++ tailWord_2232782) baseStart_2232782 baseEnd_2232782 := by
    simpa [prefixWord, tailWord_2232782, baseEnd_2232782] using wordTrace_append hprefix tailTrace_2232782
  have hstable : (prefixWord ++ tailWord_2232782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232782).length < 2 ^ (prefixWord ++ tailWord_2232782).sum := by decide
  have hdescent : baseEnd_2232782 < baseStart_2232782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232799 : List Nat := [1, 1, 2, 3, 3, 2, 4, 1, 2, 3]
def baseStart_2232799 : Nat := 118140960795 + 2232799 * 2 ^ 59
def prefixEnd_2232799 : Nat := 4983230072969 + 3 ^ 40 * 2232799 * 2
def baseEnd_2232799 : Nat := 764332727918876598229367

theorem tailTrace_2232799 : CollatzResearch.WordTrace tailWord_2232799 prefixEnd_2232799 764332727918876598229367 := by
  unfold tailWord_2232799
  simp only [CollatzResearch.WordTrace]
  refine ⟨81436869837958029554941451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54291246558638686369960967 81436869837958029554941451)
  ·
    refine ⟨122155304756937044332412177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81436869837958029554941451 122155304756937044332412177)
    ·
      refine ⟨91616478567702783249309133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122155304756937044332412177 91616478567702783249309133)
      ·
        refine ⟨34356179462888543718490925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91616478567702783249309133 34356179462888543718490925)
        ·
          refine ⟨12883567298583203894434097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34356179462888543718490925 12883567298583203894434097)
          ·
            refine ⟨9662675473937402920825573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12883567298583203894434097 9662675473937402920825573)
            ·
              refine ⟨1811751651363263047654795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9662675473937402920825573 1811751651363263047654795)
              ·
                refine ⟨2717627477044894571482193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1811751651363263047654795 2717627477044894571482193)
                ·
                  refine ⟨2038220607783670928611645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2717627477044894571482193 2038220607783670928611645)
                  ·
                    refine ⟨764332727918876598229367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2038220607783670928611645 764332727918876598229367)
                    ·
                      rfl

theorem cell22_2232799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 2, 3].length) (baseStart_2232799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232799 prefixEnd_2232799 := by exact prefixLift 2232799
  have htrace : WordTrace (prefixWord ++ tailWord_2232799) baseStart_2232799 baseEnd_2232799 := by
    simpa [prefixWord, tailWord_2232799, baseEnd_2232799] using wordTrace_append hprefix tailTrace_2232799
  have hstable : (prefixWord ++ tailWord_2232799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232799).length < 2 ^ (prefixWord ++ tailWord_2232799).sum := by decide
  have hdescent : baseEnd_2232799 < baseStart_2232799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232878 : List Nat := [4, 1, 3, 1, 3, 1, 2, 3, 1, 3]
def baseStart_2232878 : Nat := 118140960795 + 2232878 * 2 ^ 59
def prefixEnd_2232878 : Nat := 4983230072969 + 3 ^ 40 * 2232878 * 2
def baseEnd_2232878 : Nat := 764359771233346725504125

theorem tailTrace_2232878 : CollatzResearch.WordTrace tailWord_2232878 prefixEnd_2232878 764359771233346725504125 := by
  unfold tailWord_2232878
  simp only [CollatzResearch.WordTrace]
  refine ⟨10179968900583978255883411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54293167469781217364711525 10179968900583978255883411)
  ·
    refine ⟨15269953350875967383825117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10179968900583978255883411 15269953350875967383825117)
    ·
      refine ⟨5726232506578487768934419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15269953350875967383825117 5726232506578487768934419)
      ·
        refine ⟨8589348759867731653401629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5726232506578487768934419 8589348759867731653401629)
        ·
          refine ⟨3221005784950399370025611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8589348759867731653401629 3221005784950399370025611)
          ·
            refine ⟨4831508677425599055038417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3221005784950399370025611 4831508677425599055038417)
            ·
              refine ⟨3623631508069199291278813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4831508677425599055038417 3623631508069199291278813)
              ·
                refine ⟨1358861815525949734229555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3623631508069199291278813 1358861815525949734229555)
                ·
                  refine ⟨2038292723288924601344333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1358861815525949734229555 2038292723288924601344333)
                  ·
                    refine ⟨764359771233346725504125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2038292723288924601344333 764359771233346725504125)
                    ·
                      rfl

theorem cell22_2232878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_2232878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232878 prefixEnd_2232878 := by exact prefixLift 2232878
  have htrace : WordTrace (prefixWord ++ tailWord_2232878) baseStart_2232878 baseEnd_2232878 := by
    simpa [prefixWord, tailWord_2232878, baseEnd_2232878] using wordTrace_append hprefix tailTrace_2232878
  have hstable : (prefixWord ++ tailWord_2232878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232878).length < 2 ^ (prefixWord ++ tailWord_2232878).sum := by decide
  have hdescent : baseEnd_2232878 < baseStart_2232878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232885 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 8]
def baseStart_2232885 : Nat := 118140960795 + 2232885 * 2 ^ 59
def prefixEnd_2232885 : Nat := 4983230072969 + 3 ^ 40 * 2232885 * 2
def baseEnd_2232885 : Nat := 254787389158800346859701

theorem tailTrace_2232885 : CollatzResearch.WordTrace tailWord_2232885 prefixEnd_2232885 254787389158800346859701 := by
  unfold tailWord_2232885
  simp only [CollatzResearch.WordTrace]
  refine ⟨81440006515646466242572109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54293337677097644161714739 81440006515646466242572109)
  ·
    refine ⟨30540002443367424840964541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81440006515646466242572109 30540002443367424840964541)
    ·
      refine ⟨11452500916262784315361703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30540002443367424840964541 11452500916262784315361703)
      ·
        refine ⟨17178751374394176473042555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11452500916262784315361703 17178751374394176473042555)
        ·
          refine ⟨25768127061591264709563833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17178751374394176473042555 25768127061591264709563833)
          ·
            refine ⟨19326095296193448532172875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25768127061591264709563833 19326095296193448532172875)
            ·
              refine ⟨28989142944290172798259313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19326095296193448532172875 28989142944290172798259313)
              ·
                refine ⟨21741857208217629598694485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28989142944290172798259313 21741857208217629598694485)
                ·
                  refine ⟨254787389158800346859701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21741857208217629598694485 254787389158800346859701)
                  ·
                    rfl

theorem cell22_2232885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_2232885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232885 prefixEnd_2232885 := by exact prefixLift 2232885
  have htrace : WordTrace (prefixWord ++ tailWord_2232885) baseStart_2232885 baseEnd_2232885 := by
    simpa [prefixWord, tailWord_2232885, baseEnd_2232885] using wordTrace_append hprefix tailTrace_2232885
  have hstable : (prefixWord ++ tailWord_2232885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232885).length < 2 ^ (prefixWord ++ tailWord_2232885).sum := by decide
  have hdescent : baseEnd_2232885 < baseStart_2232885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232887 : List Nat := [1, 1, 3, 1, 2, 3, 3, 3, 1, 4]
def baseStart_2232887 : Nat := 118140960795 + 2232887 * 2 ^ 59
def prefixEnd_2232887 : Nat := 4983230072969 + 3 ^ 40 * 2232887 * 2
def baseEnd_2232887 : Nat := 764362852117273702029097

theorem tailTrace_2232887 : CollatzResearch.WordTrace tailWord_2232887 prefixEnd_2232887 764362852117273702029097 := by
  unfold tailWord_2232887
  simp only [CollatzResearch.WordTrace]
  refine ⟨81440079461639220584144915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54293386307759480389429943 81440079461639220584144915)
  ·
    refine ⟨122160119192458830876217373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81440079461639220584144915 122160119192458830876217373)
    ·
      refine ⟨45810044697172061578581515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122160119192458830876217373 45810044697172061578581515)
      ·
        refine ⟨68715067045758092367872273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45810044697172061578581515 68715067045758092367872273)
        ·
          refine ⟨51536300284318569275904205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68715067045758092367872273 51536300284318569275904205)
          ·
            refine ⟨19326112606619463478464077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51536300284318569275904205 19326112606619463478464077)
            ·
              refine ⟨7247292227482298804424029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19326112606619463478464077 7247292227482298804424029)
              ·
                refine ⟨2717734585305862051659011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7247292227482298804424029 2717734585305862051659011)
                ·
                  refine ⟨4076601877958793077488517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2717734585305862051659011 4076601877958793077488517)
                  ·
                    refine ⟨764362852117273702029097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4076601877958793077488517 764362852117273702029097)
                    ·
                      rfl

theorem cell22_2232887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_2232887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232887 prefixEnd_2232887 := by exact prefixLift 2232887
  have htrace : WordTrace (prefixWord ++ tailWord_2232887) baseStart_2232887 baseEnd_2232887 := by
    simpa [prefixWord, tailWord_2232887, baseEnd_2232887] using wordTrace_append hprefix tailTrace_2232887
  have hstable : (prefixWord ++ tailWord_2232887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232887).length < 2 ^ (prefixWord ++ tailWord_2232887).sum := by decide
  have hdescent : baseEnd_2232887 < baseStart_2232887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232917 : List Nat := [1, 3, 2, 2, 1, 1, 5, 1, 1, 5]
def baseStart_2232917 : Nat := 118140960795 + 2232917 * 2 ^ 59
def prefixEnd_2232917 : Nat := 4983230072969 + 3 ^ 40 * 2232917 * 2
def baseEnd_2232917 : Nat := 764373121730363623779005

theorem tailTrace_2232917 : CollatzResearch.WordTrace tailWord_2232917 prefixEnd_2232917 764373121730363623779005 := by
  unfold tailWord_2232917
  simp only [CollatzResearch.WordTrace]
  refine ⟨81441173651530535707737005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54294115767687023805158003 81441173651530535707737005)
  ·
    refine ⟨30540440119323950890401377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81441173651530535707737005 30540440119323950890401377)
    ·
      refine ⟨22905330089492963167801033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30540440119323950890401377 22905330089492963167801033)
      ·
        refine ⟨17178997567119722375850775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22905330089492963167801033 17178997567119722375850775)
        ·
          refine ⟨25768496350679583563776163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17178997567119722375850775 25768496350679583563776163)
          ·
            refine ⟨38652744526019375345664245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25768496350679583563776163 38652744526019375345664245)
            ·
              refine ⟨3623694799314316438656023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38652744526019375345664245 3623694799314316438656023)
              ·
                refine ⟨5435542198971474657984035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3623694799314316438656023 5435542198971474657984035)
                ·
                  refine ⟨8153313298457211986976053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5435542198971474657984035 8153313298457211986976053)
                  ·
                    refine ⟨764373121730363623779005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8153313298457211986976053 764373121730363623779005)
                    ·
                      rfl

theorem cell22_2232917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_2232917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232917 prefixEnd_2232917 := by exact prefixLift 2232917
  have htrace : WordTrace (prefixWord ++ tailWord_2232917) baseStart_2232917 baseEnd_2232917 := by
    simpa [prefixWord, tailWord_2232917, baseEnd_2232917] using wordTrace_append hprefix tailTrace_2232917
  have hstable : (prefixWord ++ tailWord_2232917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232917).length < 2 ^ (prefixWord ++ tailWord_2232917).sum := by decide
  have hdescent : baseEnd_2232917 < baseStart_2232917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232932 : List Nat := [2, 3, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_2232932 : Nat := 118140960795 + 2232932 * 2 ^ 59
def prefixEnd_2232932 : Nat := 4983230072969 + 3 ^ 40 * 2232932 * 2
def baseEnd_2232932 : Nat := 764378256536908584653959

theorem tailTrace_2232932 : CollatzResearch.WordTrace tailWord_2232932 prefixEnd_2232932 764378256536908584653959 := by
  unfold tailWord_2232932
  simp only [CollatzResearch.WordTrace]
  refine ⟨40720860373238096634766525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54294480497650795513022033 40720860373238096634766525)
  ·
    refine ⟨15270322639964286238037447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40720860373238096634766525 15270322639964286238037447)
    ·
      refine ⟨22905483959946429357056171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15270322639964286238037447 22905483959946429357056171)
      ·
        refine ⟨34358225939919644035584257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22905483959946429357056171 34358225939919644035584257)
        ·
          refine ⟨25768669454939733026688193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34358225939919644035584257 25768669454939733026688193)
          ·
            refine ⟨19326502091204799770016145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25768669454939733026688193 19326502091204799770016145)
            ·
              refine ⟨14494876568403599827512109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19326502091204799770016145 14494876568403599827512109)
              ·
                refine ⟨5435578713151349935317041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14494876568403599827512109 5435578713151349935317041)
                ·
                  refine ⟨4076684034863512451487781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5435578713151349935317041 4076684034863512451487781)
                  ·
                    refine ⟨764378256536908584653959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4076684034863512451487781 764378256536908584653959)
                    ·
                      rfl

theorem cell22_2232932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_2232932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232932 prefixEnd_2232932 := by exact prefixLift 2232932
  have htrace : WordTrace (prefixWord ++ tailWord_2232932) baseStart_2232932 baseEnd_2232932 := by
    simpa [prefixWord, tailWord_2232932, baseEnd_2232932] using wordTrace_append hprefix tailTrace_2232932
  have hstable : (prefixWord ++ tailWord_2232932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232932).length < 2 ^ (prefixWord ++ tailWord_2232932).sum := by decide
  have hdescent : baseEnd_2232932 < baseStart_2232932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2232996 : List Nat := [2, 3, 1, 2, 2, 1, 2, 5, 1, 3]
def baseStart_2232996 : Nat := 118140960795 + 2232996 * 2 ^ 59
def prefixEnd_2232996 : Nat := 4983230072969 + 3 ^ 40 * 2232996 * 2
def baseEnd_2232996 : Nat := 764400165044833751053763

theorem tailTrace_2232996 : CollatzResearch.WordTrace tailWord_2232996 prefixEnd_2232996 764400165044833751053763 := by
  unfold tailWord_2232996
  simp only [CollatzResearch.WordTrace]
  refine ⟨40722027509122166099931421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54296036678829554799908561 40722027509122166099931421)
  ·
    refine ⟨15270760315920812287474283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40722027509122166099931421 15270760315920812287474283)
    ·
      refine ⟨22906140473881218431211425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15270760315920812287474283 22906140473881218431211425)
      ·
        refine ⟨17179605355410913823408569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22906140473881218431211425 17179605355410913823408569)
        ·
          refine ⟨12884704016558185367556427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17179605355410913823408569 12884704016558185367556427)
          ·
            refine ⟨19327056024837278051334641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12884704016558185367556427 19327056024837278051334641)
            ·
              refine ⟨14495292018627958538500981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19327056024837278051334641 14495292018627958538500981)
              ·
                refine ⟨1358933626746371112984467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14495292018627958538500981 1358933626746371112984467)
                ·
                  refine ⟨2038400440119556669476701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1358933626746371112984467 2038400440119556669476701)
                  ·
                    refine ⟨764400165044833751053763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2038400440119556669476701 764400165044833751053763)
                    ·
                      rfl

theorem cell22_2232996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_2232996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2232996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2232996 prefixEnd_2232996 := by exact prefixLift 2232996
  have htrace : WordTrace (prefixWord ++ tailWord_2232996) baseStart_2232996 baseEnd_2232996 := by
    simpa [prefixWord, tailWord_2232996, baseEnd_2232996] using wordTrace_append hprefix tailTrace_2232996
  have hstable : (prefixWord ++ tailWord_2232996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2232996).length < 2 ^ (prefixWord ++ tailWord_2232996).sum := by decide
  have hdescent : baseEnd_2232996 < baseStart_2232996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2232996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233013 : List Nat := [1, 3, 3, 3, 1, 2, 1, 4, 1, 3]
def baseStart_2233013 : Nat := 118140960795 + 2233013 * 2 ^ 59
def prefixEnd_2233013 : Nat := 4983230072969 + 3 ^ 40 * 2233013 * 2
def baseEnd_2233013 : Nat := 764405984492251373378711

theorem tailTrace_2233013 : CollatzResearch.WordTrace tailWord_2233013 prefixEnd_2233013 764405984492251373378711 := by
  unfold tailWord_2233013
  simp only [CollatzResearch.WordTrace]
  refine ⟨81444675059182744103231693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54296450039455162735487795 81444675059182744103231693)
  ·
    refine ⟨30541753147193529038711885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81444675059182744103231693 30541753147193529038711885)
    ·
      refine ⟨11453157430197573389516957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30541753147193529038711885 11453157430197573389516957)
      ·
        refine ⟨4294934036324090021068859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11453157430197573389516957 4294934036324090021068859)
        ·
          refine ⟨6442401054486135031603289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4294934036324090021068859 6442401054486135031603289)
          ·
            refine ⟨4831800790864601273702467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6442401054486135031603289 4831800790864601273702467)
            ·
              refine ⟨7247701186296901910553701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4831800790864601273702467 7247701186296901910553701)
              ·
                refine ⟨1358943972430669108228819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7247701186296901910553701 1358943972430669108228819)
                ·
                  refine ⟨2038415958646003662343229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1358943972430669108228819 2038415958646003662343229)
                  ·
                    refine ⟨764405984492251373378711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2038415958646003662343229 764405984492251373378711)
                    ·
                      rfl

theorem cell22_2233013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_2233013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233013 prefixEnd_2233013 := by exact prefixLift 2233013
  have htrace : WordTrace (prefixWord ++ tailWord_2233013) baseStart_2233013 baseEnd_2233013 := by
    simpa [prefixWord, tailWord_2233013, baseEnd_2233013] using wordTrace_append hprefix tailTrace_2233013
  have hstable : (prefixWord ++ tailWord_2233013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233013).length < 2 ^ (prefixWord ++ tailWord_2233013).sum := by decide
  have hdescent : baseEnd_2233013 < baseStart_2233013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233030 : List Nat := [6, 1, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_2233030 : Nat := 118140960795 + 2233030 * 2 ^ 59
def prefixEnd_2233030 : Nat := 4983230072969 + 3 ^ 40 * 2233030 * 2
def baseEnd_2233030 : Nat := 764411803939668995703659

theorem tailTrace_2233030 : CollatzResearch.WordTrace tailWord_2233030 prefixEnd_2233030 764411803939668995703659 := by
  unfold tailWord_2233030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2545165471878786125206267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54296863400080770671067029 2545165471878786125206267)
  ·
    refine ⟨3817748207818179187809401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2545165471878786125206267 3817748207818179187809401)
    ·
      refine ⟨2863311155863634390857051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3817748207818179187809401 2863311155863634390857051)
      ·
        refine ⟨4294966733795451586285577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2863311155863634390857051 4294966733795451586285577)
        ·
          refine ⟨3221225050346588689714183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4294966733795451586285577 3221225050346588689714183)
          ·
            refine ⟨4831837575519883034571275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3221225050346588689714183 4831837575519883034571275)
            ·
              refine ⟨7247756363279824551856913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4831837575519883034571275 7247756363279824551856913)
              ·
                refine ⟨5435817272459868413892685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7247756363279824551856913 5435817272459868413892685)
                ·
                  refine ⟨2038431477172450655209757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5435817272459868413892685 2038431477172450655209757)
                  ·
                    refine ⟨764411803939668995703659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2038431477172450655209757 764411803939668995703659)
                    ·
                      rfl

theorem cell22_2233030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_2233030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233030 prefixEnd_2233030 := by exact prefixLift 2233030
  have htrace : WordTrace (prefixWord ++ tailWord_2233030) baseStart_2233030 baseEnd_2233030 := by
    simpa [prefixWord, tailWord_2233030, baseEnd_2233030] using wordTrace_append hprefix tailTrace_2233030
  have hstable : (prefixWord ++ tailWord_2233030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233030).length < 2 ^ (prefixWord ++ tailWord_2233030).sum := by decide
  have hdescent : baseEnd_2233030 < baseStart_2233030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233067 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 4, 4]
def baseStart_2233067 : Nat := 118140960795 + 2233067 * 2 ^ 59
def prefixEnd_2233067 : Nat := 4983230072969 + 3 ^ 40 * 2233067 * 2
def baseEnd_2233067 : Nat := 764424469795813232528545

theorem tailTrace_2233067 : CollatzResearch.WordTrace tailWord_2233067 prefixEnd_2233067 764424469795813232528545 := by
  unfold tailWord_2233067
  simp only [CollatzResearch.WordTrace]
  refine ⟨81446644600987111325697455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54297763067324740883798303 81446644600987111325697455)
  ·
    refine ⟨122169966901480666988546183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81446644600987111325697455 122169966901480666988546183)
    ·
      refine ⟨183254950352221000482819275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122169966901480666988546183 183254950352221000482819275)
      ·
        refine ⟨274882425528331500724228913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183254950352221000482819275 274882425528331500724228913)
        ·
          refine ⟨206161819146248625543171685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274882425528331500724228913 206161819146248625543171685)
          ·
            refine ⟨38655341089921617289344691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206161819146248625543171685 38655341089921617289344691)
            ·
              refine ⟨57983011634882425934017037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38655341089921617289344691 57983011634882425934017037)
              ·
                refine ⟨21743629363080909725256389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57983011634882425934017037 21743629363080909725256389)
                ·
                  refine ⟨4076930505577670573485573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21743629363080909725256389 4076930505577670573485573)
                  ·
                    refine ⟨764424469795813232528545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4076930505577670573485573 764424469795813232528545)
                    ·
                      rfl

theorem cell22_2233067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 4].length) (baseStart_2233067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233067 prefixEnd_2233067 := by exact prefixLift 2233067
  have htrace : WordTrace (prefixWord ++ tailWord_2233067) baseStart_2233067 baseEnd_2233067 := by
    simpa [prefixWord, tailWord_2233067, baseEnd_2233067] using wordTrace_append hprefix tailTrace_2233067
  have hstable : (prefixWord ++ tailWord_2233067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233067).length < 2 ^ (prefixWord ++ tailWord_2233067).sum := by decide
  have hdescent : baseEnd_2233067 < baseStart_2233067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233086 : List Nat := [4, 2, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_2233086 : Nat := 118140960795 + 2233086 * 2 ^ 59
def prefixEnd_2233086 : Nat := 4983230072969 + 3 ^ 40 * 2233086 * 2
def baseEnd_2233086 : Nat := 764430973884103516303487

theorem tailTrace_2233086 : CollatzResearch.WordTrace tailWord_2233086 prefixEnd_2233086 764430973884103516303487 := by
  unfold tailWord_2233086
  simp only [CollatzResearch.WordTrace]
  refine ⟨10180917198489784696329889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54298225058612185047092741 10180917198489784696329889)
  ·
    refine ⟨7635687898867338522247417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10180917198489784696329889 7635687898867338522247417)
    ·
      refine ⟨5726765924150503891685563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7635687898867338522247417 5726765924150503891685563)
      ·
        refine ⟨8590148886225755837528345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5726765924150503891685563 8590148886225755837528345)
        ·
          refine ⟨6442611664669316878146259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8590148886225755837528345 6442611664669316878146259)
          ·
            refine ⟨9663917497003975317219389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6442611664669316878146259 9663917497003975317219389)
            ·
              refine ⟨3623969061376490743957271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9663917497003975317219389 3623969061376490743957271)
              ·
                refine ⟨5435953592064736115935907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3623969061376490743957271 5435953592064736115935907)
                ·
                  refine ⟨8153930388097104173903861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5435953592064736115935907 8153930388097104173903861)
                  ·
                    refine ⟨764430973884103516303487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8153930388097104173903861 764430973884103516303487)
                    ·
                      rfl

theorem cell22_2233086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_2233086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233086 prefixEnd_2233086 := by exact prefixLift 2233086
  have htrace : WordTrace (prefixWord ++ tailWord_2233086) baseStart_2233086 baseEnd_2233086 := by
    simpa [prefixWord, tailWord_2233086, baseEnd_2233086] using wordTrace_append hprefix tailTrace_2233086
  have hstable : (prefixWord ++ tailWord_2233086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233086).length < 2 ^ (prefixWord ++ tailWord_2233086).sum := by decide
  have hdescent : baseEnd_2233086 < baseStart_2233086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233112 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 1, 8]
def baseStart_2233112 : Nat := 118140960795 + 2233112 * 2 ^ 59
def prefixEnd_2233112 : Nat := 4983230072969 + 3 ^ 40 * 2233112 * 2
def baseEnd_2233112 : Nat := 764439874215448115153407

theorem tailTrace_2233112 : CollatzResearch.WordTrace tailWord_2233112 prefixEnd_2233112 764439874215448115153407 := by
  unfold tailWord_2233112
  simp only [CollatzResearch.WordTrace]
  refine ⟨40724142942912042005542795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54298857257216056007390393 40724142942912042005542795)
  ·
    refine ⟨61086214414368063008314193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40724142942912042005542795 61086214414368063008314193)
    ·
      refine ⟨45814660810776047256235645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61086214414368063008314193 45814660810776047256235645)
      ·
        refine ⟨17180497804041017721088367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45814660810776047256235645 17180497804041017721088367)
        ·
          refine ⟨25770746706061526581632551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17180497804041017721088367 25770746706061526581632551)
          ·
            refine ⟨38656120059092289872448827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25770746706061526581632551 38656120059092289872448827)
            ·
              refine ⟨57984180088638434808673241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38656120059092289872448827 57984180088638434808673241)
              ·
                refine ⟨43488135066478826106504931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57984180088638434808673241 43488135066478826106504931)
                ·
                  refine ⟨65232202599718239159757397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43488135066478826106504931 65232202599718239159757397)
                  ·
                    refine ⟨764439874215448115153407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65232202599718239159757397 764439874215448115153407)
                    ·
                      rfl

theorem cell22_2233112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_2233112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233112 prefixEnd_2233112 := by exact prefixLift 2233112
  have htrace : WordTrace (prefixWord ++ tailWord_2233112) baseStart_2233112 baseEnd_2233112 := by
    simpa [prefixWord, tailWord_2233112, baseEnd_2233112] using wordTrace_append hprefix tailTrace_2233112
  have hstable : (prefixWord ++ tailWord_2233112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233112).length < 2 ^ (prefixWord ++ tailWord_2233112).sum := by decide
  have hdescent : baseEnd_2233112 < baseStart_2233112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233133 : List Nat := [1, 5, 3, 2, 1, 1, 2, 7]
def baseStart_2233133 : Nat := 118140960795 + 2233133 * 2 ^ 59
def prefixEnd_2233133 : Nat := 4983230072969 + 3 ^ 40 * 2233133 * 2
def baseEnd_2233133 : Nat := 84938562549401228930927

theorem tailTrace_2233133 : CollatzResearch.WordTrace tailWord_2233133 prefixEnd_2233133 84938562549401228930927 := by
  unfold tailWord_2233133
  simp only [CollatzResearch.WordTrace]
  refine ⟨81449051818748004597600053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54299367879165336398400035 81449051818748004597600053)
  ·
    refine ⟨7635848608007625431025005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81449051818748004597600053 7635848608007625431025005)
    ·
      refine ⟨2863443228002859536634377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7635848608007625431025005 2863443228002859536634377)
      ·
        refine ⟨2147582421002144652475783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2863443228002859536634377 2147582421002144652475783)
        ·
          refine ⟨3221373631503216978713675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2147582421002144652475783 3221373631503216978713675)
          ·
            refine ⟨4832060447254825468070513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3221373631503216978713675 4832060447254825468070513)
            ·
              refine ⟨3624045335441119101052885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4832060447254825468070513 3624045335441119101052885)
              ·
                refine ⟨84938562549401228930927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3624045335441119101052885 84938562549401228930927)
                ·
                  rfl

theorem cell22_2233133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 7].length) (baseStart_2233133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233133 prefixEnd_2233133 := by exact prefixLift 2233133
  have htrace : WordTrace (prefixWord ++ tailWord_2233133) baseStart_2233133 baseEnd_2233133 := by
    simpa [prefixWord, tailWord_2233133, baseEnd_2233133] using wordTrace_append hprefix tailTrace_2233133
  have hstable : (prefixWord ++ tailWord_2233133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233133).length < 2 ^ (prefixWord ++ tailWord_2233133).sum := by decide
  have hdescent : baseEnd_2233133 < baseStart_2233133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233144 : List Nat := [2, 1, 2, 1, 3, 2, 3, 3, 5]
def baseStart_2233144 : Nat := 118140960795 + 2233144 * 2 ^ 59
def prefixEnd_2233144 : Nat := 4983230072969 + 3 ^ 40 * 2233144 * 2
def baseEnd_2233144 : Nat := 254816942823136899451103

theorem tailTrace_2233144 : CollatzResearch.WordTrace tailWord_2233144 prefixEnd_2233144 254816942823136899451103 := by
  unfold tailWord_2233144
  simp only [CollatzResearch.WordTrace]
  refine ⟨40724726510854076738125243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54299635347805435650833657 40724726510854076738125243)
  ·
    refine ⟨61087089766281115107187865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40724726510854076738125243 61087089766281115107187865)
    ·
      refine ⟨45815317324710836330390899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61087089766281115107187865 45815317324710836330390899)
      ·
        refine ⟨68722975987066254495586349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45815317324710836330390899 68722975987066254495586349)
        ·
          refine ⟨25771115995149845435844881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68722975987066254495586349 25771115995149845435844881)
          ·
            refine ⟨19328336996362384076883661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25771115995149845435844881 19328336996362384076883661)
            ·
              refine ⟨7248126373635894028831373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19328336996362384076883661 7248126373635894028831373)
              ·
                refine ⟨2718047390113460260811765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7248126373635894028831373 2718047390113460260811765)
                ·
                  refine ⟨254816942823136899451103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2718047390113460260811765 254816942823136899451103)
                  ·
                    rfl

theorem cell22_2233144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 5].length) (baseStart_2233144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233144 prefixEnd_2233144 := by exact prefixLift 2233144
  have htrace : WordTrace (prefixWord ++ tailWord_2233144) baseStart_2233144 baseEnd_2233144 := by
    simpa [prefixWord, tailWord_2233144, baseEnd_2233144] using wordTrace_append hprefix tailTrace_2233144
  have hstable : (prefixWord ++ tailWord_2233144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233144).length < 2 ^ (prefixWord ++ tailWord_2233144).sum := by decide
  have hdescent : baseEnd_2233144 < baseStart_2233144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233206 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_2233206 : Nat := 118140960795 + 2233206 * 2 ^ 59
def prefixEnd_2233206 : Nat := 4983230072969 + 3 ^ 40 * 2233206 * 2
def baseEnd_2233206 : Nat := 254824017445487734434373

theorem tailTrace_2233206 : CollatzResearch.WordTrace tailWord_2233206 prefixEnd_2233206 254824017445487734434373 := by
  unfold tailWord_2233206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5090732146717721129062967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54301142898322358710004981 5090732146717721129062967)
  ·
    refine ⟨7636098220076581693594451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5090732146717721129062967 7636098220076581693594451)
    ·
      refine ⟨11454147330114872540391677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7636098220076581693594451 11454147330114872540391677)
      ·
        refine ⟨4295305248793077202646879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11454147330114872540391677 4295305248793077202646879)
        ·
          refine ⟨6442957873189615803970319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4295305248793077202646879 6442957873189615803970319)
          ·
            refine ⟨9664436809784423705955479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6442957873189615803970319 9664436809784423705955479)
            ·
              refine ⟨14496655214676635558933219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9664436809784423705955479 14496655214676635558933219)
              ·
                refine ⟨21744982822014953338399829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14496655214676635558933219 21744982822014953338399829)
                ·
                  refine ⟨254824017445487734434373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21744982822014953338399829 254824017445487734434373)
                  ·
                    rfl

theorem cell22_2233206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_2233206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233206 prefixEnd_2233206 := by exact prefixLift 2233206
  have htrace : WordTrace (prefixWord ++ tailWord_2233206) baseStart_2233206 baseEnd_2233206 := by
    simpa [prefixWord, tailWord_2233206, baseEnd_2233206] using wordTrace_append hprefix tailTrace_2233206
  have hstable : (prefixWord ++ tailWord_2233206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233206).length < 2 ^ (prefixWord ++ tailWord_2233206).sum := by decide
  have hdescent : baseEnd_2233206 < baseStart_2233206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233219 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 1, 6]
def baseStart_2233219 : Nat := 118140960795 + 2233219 * 2 ^ 59
def prefixEnd_2233219 : Nat := 4983230072969 + 3 ^ 40 * 2233219 * 2
def baseEnd_2233219 : Nat := 764476502502135502728079

theorem tailTrace_2233219 : CollatzResearch.WordTrace tailWord_2233219 prefixEnd_2233219 764476502502135502728079 := by
  unfold tailWord_2233219
  simp only [CollatzResearch.WordTrace]
  refine ⟨81452188496436441285230711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54301458997624294190153807 81452188496436441285230711)
  ·
    refine ⟨122178282744654661927846067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81452188496436441285230711 122178282744654661927846067)
    ·
      refine ⟨183267424116981992891769101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122178282744654661927846067 183267424116981992891769101)
      ·
        refine ⟨68725284043868247334413413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183267424116981992891769101 68725284043868247334413413)
        ·
          refine ⟨12885990758225296375202515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68725284043868247334413413 12885990758225296375202515)
          ·
            refine ⟨19328986137337944562803773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12885990758225296375202515 19328986137337944562803773)
            ·
              refine ⟨7248369801501729211051415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19328986137337944562803773 7248369801501729211051415)
              ·
                refine ⟨10872554702252593816577123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7248369801501729211051415 10872554702252593816577123)
                ·
                  refine ⟨16308832053378890724865685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10872554702252593816577123 16308832053378890724865685)
                  ·
                    refine ⟨764476502502135502728079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16308832053378890724865685 764476502502135502728079)
                    ·
                      rfl

theorem cell22_2233219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 6].length) (baseStart_2233219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233219 prefixEnd_2233219 := by exact prefixLift 2233219
  have htrace : WordTrace (prefixWord ++ tailWord_2233219) baseStart_2233219 baseEnd_2233219 := by
    simpa [prefixWord, tailWord_2233219, baseEnd_2233219] using wordTrace_append hprefix tailTrace_2233219
  have hstable : (prefixWord ++ tailWord_2233219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233219).length < 2 ^ (prefixWord ++ tailWord_2233219).sum := by decide
  have hdescent : baseEnd_2233219 < baseStart_2233219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233223 : List Nat := [1, 1, 4, 2, 3, 2, 2, 3, 4]
def baseStart_2233223 : Nat := 118140960795 + 2233223 * 2 ^ 59
def prefixEnd_2233223 : Nat := 4983230072969 + 3 ^ 40 * 2233223 * 2
def baseEnd_2233223 : Nat := 254825957261293608542689

theorem tailTrace_2233223 : CollatzResearch.WordTrace tailWord_2233223 prefixEnd_2233223 254825957261293608542689 := by
  unfold tailWord_2233223
  simp only [CollatzResearch.WordTrace]
  refine ⟨81452334388421949968376323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54301556258947966645584215 81452334388421949968376323)
  ·
    refine ⟨122178501582632924952564485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81452334388421949968376323 122178501582632924952564485)
    ·
      refine ⟨22908469046743673428605841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122178501582632924952564485 22908469046743673428605841)
      ·
        refine ⟨17181351785057755071454381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22908469046743673428605841 17181351785057755071454381)
        ·
          refine ⟨6443006919396658151795393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17181351785057755071454381 6443006919396658151795393)
          ·
            refine ⟨4832255189547493613846545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6443006919396658151795393 4832255189547493613846545)
            ·
              refine ⟨3624191392160620210384909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4832255189547493613846545 3624191392160620210384909)
              ·
                refine ⟨1359071772060232578894341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3624191392160620210384909 1359071772060232578894341)
                ·
                  refine ⟨254825957261293608542689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1359071772060232578894341 254825957261293608542689)
                  ·
                    rfl

theorem cell22_2233223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 4].length) (baseStart_2233223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233223 prefixEnd_2233223 := by exact prefixLift 2233223
  have htrace : WordTrace (prefixWord ++ tailWord_2233223) baseStart_2233223 baseEnd_2233223 := by
    simpa [prefixWord, tailWord_2233223, baseEnd_2233223] using wordTrace_append hprefix tailTrace_2233223
  have hstable : (prefixWord ++ tailWord_2233223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233223).length < 2 ^ (prefixWord ++ tailWord_2233223).sum := by decide
  have hdescent : baseEnd_2233223 < baseStart_2233223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233236 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2233236 : Nat := 118140960795 + 2233236 * 2 ^ 59
def prefixEnd_2233236 : Nat := 4983230072969 + 3 ^ 40 * 2233236 * 2
def baseEnd_2233236 : Nat := 764482321949553125053027

theorem tailTrace_2233236 : CollatzResearch.WordTrace tailWord_2233236 prefixEnd_2233236 764482321949553125053027 := by
  unfold tailWord_2233236
  simp only [CollatzResearch.WordTrace]
  refine ⟨40726404268687426594299781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54301872358249902125733041 40726404268687426594299781)
  ·
    refine ⟨7636200800378892486431209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40726404268687426594299781 7636200800378892486431209)
    ·
      refine ⟨5727150600284169364823407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7636200800378892486431209 5727150600284169364823407)
      ·
        refine ⟨8590725900426254047235111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5727150600284169364823407 8590725900426254047235111)
        ·
          refine ⟨12886088850639381070852667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8590725900426254047235111 12886088850639381070852667)
          ·
            refine ⟨19329133275959071606279001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12886088850639381070852667 19329133275959071606279001)
            ·
              refine ⟨14496849956969303704709251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19329133275959071606279001 14496849956969303704709251)
              ·
                refine ⟨21745274935453955557063877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14496849956969303704709251 21745274935453955557063877)
                ·
                  refine ⟨4077239050397616666949477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21745274935453955557063877 4077239050397616666949477)
                  ·
                    refine ⟨764482321949553125053027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4077239050397616666949477 764482321949553125053027)
                    ·
                      rfl

theorem cell22_2233236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2233236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233236 prefixEnd_2233236 := by exact prefixLift 2233236
  have htrace : WordTrace (prefixWord ++ tailWord_2233236) baseStart_2233236 baseEnd_2233236 := by
    simpa [prefixWord, tailWord_2233236, baseEnd_2233236] using wordTrace_append hprefix tailTrace_2233236
  have hstable : (prefixWord ++ tailWord_2233236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233236).length < 2 ^ (prefixWord ++ tailWord_2233236).sum := by decide
  have hdescent : baseEnd_2233236 < baseStart_2233236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233255 : List Nat := [1, 1, 6, 1, 4, 1, 1, 1, 1, 5]
def baseStart_2233255 : Nat := 118140960795 + 2233255 * 2 ^ 59
def prefixEnd_2233255 : Nat := 4983230072969 + 3 ^ 40 * 2233255 * 2
def baseEnd_2233255 : Nat := 764488826037843408827969

theorem tailTrace_2233255 : CollatzResearch.WordTrace tailWord_2233255 prefixEnd_2233255 764488826037843408827969 := by
  unfold tailWord_2233255
  simp only [CollatzResearch.WordTrace]
  refine ⟨81453501524306019433541219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54302334349537346289027479 81453501524306019433541219)
  ·
    refine ⟨122180252286459029150311829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81453501524306019433541219 122180252286459029150311829)
    ·
      refine ⟨5727199325927766991420867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 122180252286459029150311829 5727199325927766991420867)
      ·
        refine ⟨8590798988891650487131301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5727199325927766991420867 8590798988891650487131301)
        ·
          refine ⟨1610774810417184466337119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8590798988891650487131301 1610774810417184466337119)
          ·
            refine ⟨2416162215625776699505679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1610774810417184466337119 2416162215625776699505679)
            ·
              refine ⟨3624243323438665049258519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2416162215625776699505679 3624243323438665049258519)
              ·
                refine ⟨5436364985157997573887779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3624243323438665049258519 5436364985157997573887779)
                ·
                  refine ⟨8154547477736996360831669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5436364985157997573887779 8154547477736996360831669)
                  ·
                    refine ⟨764488826037843408827969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8154547477736996360831669 764488826037843408827969)
                    ·
                      rfl

theorem cell22_2233255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_2233255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233255 prefixEnd_2233255 := by exact prefixLift 2233255
  have htrace : WordTrace (prefixWord ++ tailWord_2233255) baseStart_2233255 baseEnd_2233255 := by
    simpa [prefixWord, tailWord_2233255, baseEnd_2233255] using wordTrace_append hprefix tailTrace_2233255
  have hstable : (prefixWord ++ tailWord_2233255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233255).length < 2 ^ (prefixWord ++ tailWord_2233255).sum := by decide
  have hdescent : baseEnd_2233255 < baseStart_2233255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233268 : List Nat := [2, 5, 2, 1, 1, 2, 1, 8]
def baseStart_2233268 : Nat := 118140960795 + 2233268 * 2 ^ 59
def prefixEnd_2233268 : Nat := 4983230072969 + 3 ^ 40 * 2233268 * 2
def baseEnd_2233268 : Nat := 84943697355946189805881

theorem tailTrace_2233268 : CollatzResearch.WordTrace tailWord_2233268 prefixEnd_2233268 84943697355946189805881 := by
  unfold tailWord_2233268
  simp only [CollatzResearch.WordTrace]
  refine ⟨40726987836629461326882229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54302650448839281769176305 40726987836629461326882229)
  ·
    refine ⟨3818155109684011999395209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40726987836629461326882229 3818155109684011999395209)
    ·
      refine ⟨2863616332263008999546407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3818155109684011999395209 2863616332263008999546407)
      ·
        refine ⟨4295424498394513499319611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2863616332263008999546407 4295424498394513499319611)
        ·
          refine ⟨6443136747591770248979417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4295424498394513499319611 6443136747591770248979417)
          ·
            refine ⟨4832352560693827686734563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6443136747591770248979417 4832352560693827686734563)
            ·
              refine ⟨7248528841040741530101845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4832352560693827686734563 7248528841040741530101845)
              ·
                refine ⟨84943697355946189805881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7248528841040741530101845 84943697355946189805881)
                ·
                  rfl

theorem cell22_2233268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 8].length) (baseStart_2233268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233268 prefixEnd_2233268 := by exact prefixLift 2233268
  have htrace : WordTrace (prefixWord ++ tailWord_2233268) baseStart_2233268 baseEnd_2233268 := by
    simpa [prefixWord, tailWord_2233268, baseEnd_2233268] using wordTrace_append hprefix tailTrace_2233268
  have hstable : (prefixWord ++ tailWord_2233268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233268).length < 2 ^ (prefixWord ++ tailWord_2233268).sum := by decide
  have hdescent : baseEnd_2233268 < baseStart_2233268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233300 : List Nat := [2, 4, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_2233300 : Nat := 118140960795 + 2233300 * 2 ^ 59
def prefixEnd_2233300 : Nat := 4983230072969 + 3 ^ 40 * 2233300 * 2
def baseEnd_2233300 : Nat := 764504230457478291452831

theorem tailTrace_2233300 : CollatzResearch.WordTrace tailWord_2233300 prefixEnd_2233300 764504230457478291452831 := by
  unfold tailWord_2233300
  simp only [CollatzResearch.WordTrace]
  refine ⟨40727571404571496059464677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54303428539428661412619569 40727571404571496059464677)
  ·
    refine ⟨7636419638357155511149627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40727571404571496059464677 7636419638357155511149627)
    ·
      refine ⟨11454629457535733266724441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7636419638357155511149627 11454629457535733266724441)
      ·
        refine ⟨8590972093151799950043331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11454629457535733266724441 8590972093151799950043331)
        ·
          refine ⟨12886458139727699925064997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8590972093151799950043331 12886458139727699925064997)
          ·
            refine ⟨2416210901198943735949687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12886458139727699925064997 2416210901198943735949687)
            ·
              refine ⟨3624316351798415603924531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2416210901198943735949687 3624316351798415603924531)
              ·
                refine ⟨5436474527697623405886797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3624316351798415603924531 5436474527697623405886797)
                ·
                  refine ⟨2038677947886608777207549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5436474527697623405886797 2038677947886608777207549)
                  ·
                    refine ⟨764504230457478291452831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2038677947886608777207549 764504230457478291452831)
                    ·
                      rfl

theorem cell22_2233300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_2233300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233300 prefixEnd_2233300 := by exact prefixLift 2233300
  have htrace : WordTrace (prefixWord ++ tailWord_2233300) baseStart_2233300 baseEnd_2233300 := by
    simpa [prefixWord, tailWord_2233300, baseEnd_2233300] using wordTrace_append hprefix tailTrace_2233300
  have hstable : (prefixWord ++ tailWord_2233300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233300).length < 2 ^ (prefixWord ++ tailWord_2233300).sum := by decide
  have hdescent : baseEnd_2233300 < baseStart_2233300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233362 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 2, 5]
def baseStart_2233362 : Nat := 118140960795 + 2233362 * 2 ^ 59
def prefixEnd_2233362 : Nat := 4983230072969 + 3 ^ 40 * 2233362 * 2
def baseEnd_2233362 : Nat := 764525454324530796402641

theorem tailTrace_2233362 : CollatzResearch.WordTrace tailWord_2233362 prefixEnd_2233362 764525454324530796402641 := by
  unfold tailWord_2233362
  simp only [CollatzResearch.WordTrace]
  refine ⟨20364351033729594176921585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54304936089945584471790893 20364351033729594176921585)
  ·
    refine ⟨15273263275297195632691189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20364351033729594176921585 15273263275297195632691189)
    ·
      refine ⟨1431868432059112090564799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15273263275297195632691189 1431868432059112090564799)
      ·
        refine ⟨2147802648088668135847199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1431868432059112090564799 2147802648088668135847199)
        ·
          refine ⟨3221703972133002203770799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2147802648088668135847199 3221703972133002203770799)
          ·
            refine ⟨4832555958199503305656199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3221703972133002203770799 4832555958199503305656199)
            ·
              refine ⟨7248833937299254958484299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4832555958199503305656199 7248833937299254958484299)
              ·
                refine ⟨10873250905948882437726449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7248833937299254958484299 10873250905948882437726449)
                ·
                  refine ⟨8154938179461661828294837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10873250905948882437726449 8154938179461661828294837)
                  ·
                    refine ⟨764525454324530796402641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8154938179461661828294837 764525454324530796402641)
                    ·
                      rfl

theorem cell22_2233362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_2233362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233362 prefixEnd_2233362 := by exact prefixLift 2233362
  have htrace : WordTrace (prefixWord ++ tailWord_2233362) baseStart_2233362 baseEnd_2233362 := by
    simpa [prefixWord, tailWord_2233362, baseEnd_2233362] using wordTrace_append hprefix tailTrace_2233362
  have hstable : (prefixWord ++ tailWord_2233362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233362).length < 2 ^ (prefixWord ++ tailWord_2233362).sum := by decide
  have hdescent : baseEnd_2233362 < baseStart_2233362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233418 : List Nat := [3, 1, 2, 1, 1, 2, 3, 3, 3, 3]
def baseStart_2233418 : Nat := 118140960795 + 2233418 * 2 ^ 59
def prefixEnd_2233418 : Nat := 4983230072969 + 3 ^ 40 * 2233418 * 2
def baseEnd_2233418 : Nat := 764544624268965317002469

theorem tailTrace_2233418 : CollatzResearch.WordTrace tailWord_2233418 prefixEnd_2233418 764544624268965317002469 := by
  unfold tailWord_2233418
  simp only [CollatzResearch.WordTrace]
  refine ⟨20364861655678874567931227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54306297748476998847816605 20364861655678874567931227)
  ·
    refine ⟨30547292483518311851896841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20364861655678874567931227 30547292483518311851896841)
    ·
      refine ⟨22910469362638733888922631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30547292483518311851896841 22910469362638733888922631)
      ·
        refine ⟨34365704043958100833383947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22910469362638733888922631 34365704043958100833383947)
        ·
          refine ⟨51548556065937151250075921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34365704043958100833383947 51548556065937151250075921)
          ·
            refine ⟨38661417049452863437556941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51548556065937151250075921 38661417049452863437556941)
            ·
              refine ⟨14498031393544823789083853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38661417049452863437556941 14498031393544823789083853)
              ·
                refine ⟨5436761772579308920906445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14498031393544823789083853 5436761772579308920906445)
                ·
                  refine ⟨2038785664717240845339917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5436761772579308920906445 2038785664717240845339917)
                  ·
                    refine ⟨764544624268965317002469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2038785664717240845339917 764544624268965317002469)
                    ·
                      rfl

theorem cell22_2233418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_2233418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233418 prefixEnd_2233418 := by exact prefixLift 2233418
  have htrace : WordTrace (prefixWord ++ tailWord_2233418) baseStart_2233418 baseEnd_2233418 := by
    simpa [prefixWord, tailWord_2233418, baseEnd_2233418] using wordTrace_append hprefix tailTrace_2233418
  have hstable : (prefixWord ++ tailWord_2233418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233418).length < 2 ^ (prefixWord ++ tailWord_2233418).sum := by decide
  have hdescent : baseEnd_2233418 < baseStart_2233418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233437 : List Nat := [1, 4, 4, 1, 2, 2, 2, 6]
def baseStart_2233437 : Nat := 118140960795 + 2233437 * 2 ^ 59
def prefixEnd_2233437 : Nat := 4983230072969 + 3 ^ 40 * 2233437 * 2
def baseEnd_2233437 : Nat := 84950125373028400086379

theorem tailTrace_2233437 : CollatzResearch.WordTrace tailWord_2233437 prefixEnd_2233437 84950125373028400086379 := by
  unfold tailWord_2233437
  simp only [CollatzResearch.WordTrace]
  refine ⟨81460139609646664516666565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54306759739764443011111043 81460139609646664516666565)
  ·
    refine ⟨15273776176808749596874981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81460139609646664516666565 15273776176808749596874981)
    ·
      refine ⟨2863833033151640549414059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15273776176808749596874981 2863833033151640549414059)
      ·
        refine ⟨4295749549727460824121089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2863833033151640549414059 4295749549727460824121089)
        ·
          refine ⟨3221812162295595618090817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4295749549727460824121089 3221812162295595618090817)
          ·
            refine ⟨2416359121721696713568113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3221812162295595618090817 2416359121721696713568113)
            ·
              refine ⟨1812269341291272535176085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2416359121721696713568113 1812269341291272535176085)
              ·
                refine ⟨84950125373028400086379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1812269341291272535176085 84950125373028400086379)
                ·
                  rfl

theorem cell22_2233437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 6].length) (baseStart_2233437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233437 prefixEnd_2233437 := by exact prefixLift 2233437
  have htrace : WordTrace (prefixWord ++ tailWord_2233437) baseStart_2233437 baseEnd_2233437 := by
    simpa [prefixWord, tailWord_2233437, baseEnd_2233437] using wordTrace_append hprefix tailTrace_2233437
  have hstable : (prefixWord ++ tailWord_2233437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233437).length < 2 ^ (prefixWord ++ tailWord_2233437).sum := by decide
  have hdescent : baseEnd_2233437 < baseStart_2233437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233495 : List Nat := [1, 1, 3, 3, 3, 1, 3, 2, 1, 4]
def baseStart_2233495 : Nat := 118140960795 + 2233495 * 2 ^ 59
def prefixEnd_2233495 : Nat := 4983230072969 + 3 ^ 40 * 2233495 * 2
def baseEnd_2233495 : Nat := 764570982942562782827233

theorem tailTrace_2233495 : CollatzResearch.WordTrace tailWord_2233495 prefixEnd_2233495 764570982942562782827233 := by
  unfold tailWord_2233495
  simp only [CollatzResearch.WordTrace]
  refine ⟨81462255043436540422277939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54308170028957693614851959 81462255043436540422277939)
  ·
    refine ⟨122193382565154810633416909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81462255043436540422277939 122193382565154810633416909)
    ·
      refine ⟨45822518461933053987531341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122193382565154810633416909 45822518461933053987531341)
      ·
        refine ⟨17183444423224895245324253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45822518461933053987531341 17183444423224895245324253)
        ·
          refine ⟨6443791658709335716996595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17183444423224895245324253 6443791658709335716996595)
          ·
            refine ⟨9665687488064003575494893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6443791658709335716996595 9665687488064003575494893)
            ·
              refine ⟨3624632808024001340810585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9665687488064003575494893 3624632808024001340810585)
              ·
                refine ⟨2718474606018001005607939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3624632808024001340810585 2718474606018001005607939)
                ·
                  refine ⟨4077711909027001508411909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2718474606018001005607939 4077711909027001508411909)
                  ·
                    refine ⟨764570982942562782827233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4077711909027001508411909 764570982942562782827233)
                    ·
                      rfl

theorem cell22_2233495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_2233495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233495 prefixEnd_2233495 := by exact prefixLift 2233495
  have htrace : WordTrace (prefixWord ++ tailWord_2233495) baseStart_2233495 baseEnd_2233495 := by
    simpa [prefixWord, tailWord_2233495, baseEnd_2233495] using wordTrace_append hprefix tailTrace_2233495
  have hstable : (prefixWord ++ tailWord_2233495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233495).length < 2 ^ (prefixWord ++ tailWord_2233495).sum := by decide
  have hdescent : baseEnd_2233495 < baseStart_2233495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233508 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_2233508 : Nat := 118140960795 + 2233508 * 2 ^ 59
def prefixEnd_2233508 : Nat := 4983230072969 + 3 ^ 40 * 2233508 * 2
def baseEnd_2233508 : Nat := 764575433108235082252193

theorem tailTrace_2233508 : CollatzResearch.WordTrace tailWord_2233508 prefixEnd_2233508 764575433108235082252193 := by
  unfold tailWord_2233508
  simp only [CollatzResearch.WordTrace]
  refine ⟨40731364596194721821250589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54308486128259629095000785 40731364596194721821250589)
  ·
    refine ⟨15274261723573020682968971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40731364596194721821250589 15274261723573020682968971)
    ·
      refine ⟨22911392585359531024453457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15274261723573020682968971 22911392585359531024453457)
      ·
        refine ⟨17183544439019648268340093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22911392585359531024453457 17183544439019648268340093)
        ·
          refine ⟨6443829164632368100627535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17183544439019648268340093 6443829164632368100627535)
          ·
            refine ⟨9665743746948552150941303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6443829164632368100627535 9665743746948552150941303)
            ·
              refine ⟨14498615620422828226411955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9665743746948552150941303 14498615620422828226411955)
              ·
                refine ⟨21747923430634242339617933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14498615620422828226411955 21747923430634242339617933)
                ·
                  refine ⟨8155471286487840877356725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21747923430634242339617933 8155471286487840877356725)
                  ·
                    refine ⟨764575433108235082252193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8155471286487840877356725 764575433108235082252193)
                    ·
                      rfl

theorem cell22_2233508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_2233508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233508 prefixEnd_2233508 := by exact prefixLift 2233508
  have htrace : WordTrace (prefixWord ++ tailWord_2233508) baseStart_2233508 baseEnd_2233508 := by
    simpa [prefixWord, tailWord_2233508, baseEnd_2233508] using wordTrace_append hprefix tailTrace_2233508
  have hstable : (prefixWord ++ tailWord_2233508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233508).length < 2 ^ (prefixWord ++ tailWord_2233508).sum := by decide
  have hdescent : baseEnd_2233508 < baseStart_2233508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233523 : List Nat := [1, 1, 1, 2, 3, 2, 4, 2, 2, 4]
def baseStart_2233523 : Nat := 118140960795 + 2233523 * 2 ^ 59
def prefixEnd_2233523 : Nat := 4983230072969 + 3 ^ 40 * 2233523 * 2
def baseEnd_2233523 : Nat := 764580567914780043127147

theorem tailTrace_2233523 : CollatzResearch.WordTrace tailWord_2233523 prefixEnd_2233523 764580567914780043127147 := by
  unfold tailWord_2233523
  simp only [CollatzResearch.WordTrace]
  refine ⟨81463276287335101204297223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54308850858223400802864815 81463276287335101204297223)
  ·
    refine ⟨122194914431002651806445835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81463276287335101204297223 122194914431002651806445835)
    ·
      refine ⟨183292371646503977709668753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122194914431002651806445835 183292371646503977709668753)
      ·
        refine ⟨137469278734877983282251565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183292371646503977709668753 137469278734877983282251565)
        ·
          refine ⟨51550979525579243730844337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137469278734877983282251565 51550979525579243730844337)
          ·
            refine ⟨38663234644184432798133253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51550979525579243730844337 38663234644184432798133253)
            ·
              refine ⟨7249356495784581149649985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38663234644184432798133253 7249356495784581149649985)
              ·
                refine ⟨5437017371838435862237489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7249356495784581149649985 5437017371838435862237489)
                ·
                  refine ⟨4077763028878826896678117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5437017371838435862237489 4077763028878826896678117)
                  ·
                    refine ⟨764580567914780043127147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4077763028878826896678117 764580567914780043127147)
                    ·
                      rfl

theorem cell22_2233523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 4].length) (baseStart_2233523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233523 prefixEnd_2233523 := by exact prefixLift 2233523
  have htrace : WordTrace (prefixWord ++ tailWord_2233523) baseStart_2233523 baseEnd_2233523 := by
    simpa [prefixWord, tailWord_2233523, baseEnd_2233523] using wordTrace_append hprefix tailTrace_2233523
  have hstable : (prefixWord ++ tailWord_2233523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233523).length < 2 ^ (prefixWord ++ tailWord_2233523).sum := by decide
  have hdescent : baseEnd_2233523 < baseStart_2233523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233557 : List Nat := [1, 3, 2, 4, 1, 3, 1, 1, 2, 4]
def baseStart_2233557 : Nat := 118140960795 + 2233557 * 2 ^ 59
def prefixEnd_2233557 : Nat := 4983230072969 + 3 ^ 40 * 2233557 * 2
def baseEnd_2233557 : Nat := 764592206809615287777043

theorem tailTrace_2233557 : CollatzResearch.WordTrace tailWord_2233557 prefixEnd_2233557 764592206809615287777043 := by
  unfold tailWord_2233557
  simp only [CollatzResearch.WordTrace]
  refine ⟨81464516369211925011034925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54309677579474616674023283 81464516369211925011034925)
  ·
    refine ⟨30549193638454471879138097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81464516369211925011034925 30549193638454471879138097)
    ·
      refine ⟨22911895228840853909353573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30549193638454471879138097 22911895228840853909353573)
      ·
        refine ⟨4295980355407660108003795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22911895228840853909353573 4295980355407660108003795)
        ·
          refine ⟨6443970533111490162005693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4295980355407660108003795 6443970533111490162005693)
          ·
            refine ⟨2416488949916808810752135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6443970533111490162005693 2416488949916808810752135)
            ·
              refine ⟨3624733424875213216128203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2416488949916808810752135 3624733424875213216128203)
              ·
                refine ⟨5437100137312819824192305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3624733424875213216128203 5437100137312819824192305)
                ·
                  refine ⟨4077825102984614868144229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5437100137312819824192305 4077825102984614868144229)
                  ·
                    refine ⟨764592206809615287777043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4077825102984614868144229 764592206809615287777043)
                    ·
                      rfl

theorem cell22_2233557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_2233557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233557 prefixEnd_2233557 := by exact prefixLift 2233557
  have htrace : WordTrace (prefixWord ++ tailWord_2233557) baseStart_2233557 baseEnd_2233557 := by
    simpa [prefixWord, tailWord_2233557, baseEnd_2233557] using wordTrace_append hprefix tailTrace_2233557
  have hstable : (prefixWord ++ tailWord_2233557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233557).length < 2 ^ (prefixWord ++ tailWord_2233557).sum := by decide
  have hdescent : baseEnd_2233557 < baseStart_2233557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233587 : List Nat := [1, 1, 1, 2, 2, 5, 2, 4, 1, 3]
def baseStart_2233587 : Nat := 118140960795 + 2233587 * 2 ^ 59
def prefixEnd_2233587 : Nat := 4983230072969 + 3 ^ 40 * 2233587 * 2
def baseEnd_2233587 : Nat := 764602476422705209526951

theorem tailTrace_2233587 : CollatzResearch.WordTrace tailWord_2233587 prefixEnd_2233587 764602476422705209526951 := by
  unfold tailWord_2233587
  simp only [CollatzResearch.WordTrace]
  refine ⟨81465610559103240134627015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54310407039402160089751343 81465610559103240134627015)
  ·
    refine ⟨122198415838654860201940523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81465610559103240134627015 122198415838654860201940523)
    ·
      refine ⟨183297623757982290302910785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122198415838654860201940523 183297623757982290302910785)
      ·
        refine ⟨137473217818486717727183089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183297623757982290302910785 137473217818486717727183089)
        ·
          refine ⟨103104913363865038295387317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137473217818486717727183089 103104913363865038295387317)
          ·
            refine ⟨9666085627862347340192561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103104913363865038295387317 9666085627862347340192561)
            ·
              refine ⟨7249564220896760505144421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9666085627862347340192561 7249564220896760505144421)
              ·
                refine ⟨1359293291418142594714579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7249564220896760505144421 1359293291418142594714579)
                ·
                  refine ⟨2038939937127213892071869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1359293291418142594714579 2038939937127213892071869)
                  ·
                    refine ⟨764602476422705209526951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2038939937127213892071869 764602476422705209526951)
                    ·
                      rfl

theorem cell22_2233587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 1, 3].length) (baseStart_2233587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233587 prefixEnd_2233587 := by exact prefixLift 2233587
  have htrace : WordTrace (prefixWord ++ tailWord_2233587) baseStart_2233587 baseEnd_2233587 := by
    simpa [prefixWord, tailWord_2233587, baseEnd_2233587] using wordTrace_append hprefix tailTrace_2233587
  have hstable : (prefixWord ++ tailWord_2233587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233587).length < 2 ^ (prefixWord ++ tailWord_2233587).sum := by decide
  have hdescent : baseEnd_2233587 < baseStart_2233587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233628 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 8]
def baseStart_2233628 : Nat := 118140960795 + 2233628 * 2 ^ 59
def prefixEnd_2233628 : Nat := 4983230072969 + 3 ^ 40 * 2233628 * 2
def baseEnd_2233628 : Nat := 254872170520198256417275

theorem tailTrace_2233628 : CollatzResearch.WordTrace tailWord_2233628 prefixEnd_2233628 254872170520198256417275 := by
  unfold tailWord_2233628
  simp only [CollatzResearch.WordTrace]
  refine ⟨40733552975977352068434769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54311403967969802757913025 40733552975977352068434769)
  ·
    refine ⟨30550164731983014051326077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40733552975977352068434769 30550164731983014051326077)
    ·
      refine ⟨11456311774493630269247279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30550164731983014051326077 11456311774493630269247279)
      ·
        refine ⟨17184467661740445403870919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11456311774493630269247279 17184467661740445403870919)
        ·
          refine ⟨25776701492610668105806379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17184467661740445403870919 25776701492610668105806379)
          ·
            refine ⟨38665052238916002158709569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25776701492610668105806379 38665052238916002158709569)
            ·
              refine ⟨28998789179187001619032177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38665052238916002158709569 28998789179187001619032177)
              ·
                refine ⟨21749091884390251214274133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28998789179187001619032177 21749091884390251214274133)
                ·
                  refine ⟨254872170520198256417275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21749091884390251214274133 254872170520198256417275)
                  ·
                    rfl

theorem cell22_2233628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_2233628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233628 prefixEnd_2233628 := by exact prefixLift 2233628
  have htrace : WordTrace (prefixWord ++ tailWord_2233628) baseStart_2233628 baseEnd_2233628 := by
    simpa [prefixWord, tailWord_2233628, baseEnd_2233628] using wordTrace_append hprefix tailTrace_2233628
  have hstable : (prefixWord ++ tailWord_2233628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233628).length < 2 ^ (prefixWord ++ tailWord_2233628).sum := by decide
  have hdescent : baseEnd_2233628 < baseStart_2233628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233673 : List Nat := [1, 2, 1, 1, 2, 3, 4, 8]
def baseStart_2233673 : Nat := 118140960795 + 2233673 * 2 ^ 59
def prefixEnd_2233673 : Nat := 4983230072969 + 3 ^ 40 * 2233673 * 2
def baseEnd_2233673 : Nat := 84959101775581072430743

theorem tailTrace_2233673 : CollatzResearch.WordTrace tailWord_2233673 prefixEnd_2233673 84959101775581072430743 := by
  unfold tailWord_2233673
  simp only [CollatzResearch.WordTrace]
  refine ⟨81468747236791676822257673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54312498157861117881505115 81468747236791676822257673)
  ·
    refine ⟨61101560427593757616693255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81468747236791676822257673 61101560427593757616693255)
    ·
      refine ⟨91652340641390636425039883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61101560427593757616693255 91652340641390636425039883)
      ·
        refine ⟨137478510962085954637559825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91652340641390636425039883 137478510962085954637559825)
        ·
          refine ⟨103108883221564465978169869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137478510962085954637559825 103108883221564465978169869)
          ·
            refine ⟨38665831208086674741813701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103108883221564465978169869 38665831208086674741813701)
            ·
              refine ⟨7249843351516251514090069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38665831208086674741813701 7249843351516251514090069)
              ·
                refine ⟨84959101775581072430743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7249843351516251514090069 84959101775581072430743)
                ·
                  rfl

theorem cell22_2233673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 8].length) (baseStart_2233673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233673 prefixEnd_2233673 := by exact prefixLift 2233673
  have htrace : WordTrace (prefixWord ++ tailWord_2233673) baseStart_2233673 baseEnd_2233673 := by
    simpa [prefixWord, tailWord_2233673, baseEnd_2233673] using wordTrace_append hprefix tailTrace_2233673
  have hstable : (prefixWord ++ tailWord_2233673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233673).length < 2 ^ (prefixWord ++ tailWord_2233673).sum := by decide
  have hdescent : baseEnd_2233673 < baseStart_2233673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233739 : List Nat := [1, 1, 1, 1, 4, 3, 4, 3, 1, 3]
def baseStart_2233739 : Nat := 118140960795 + 2233739 * 2 ^ 59
def prefixEnd_2233739 : Nat := 4983230072969 + 3 ^ 40 * 2233739 * 2
def baseEnd_2233739 : Nat := 764654509129027479726485

theorem tailTrace_2233739 : CollatzResearch.WordTrace tailWord_2233739 prefixEnd_2233739 764654509129027479726485 := by
  unfold tailWord_2233739
  simp only [CollatzResearch.WordTrace]
  refine ⟨81471154454552570094160271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54314102969701713396106847 81471154454552570094160271)
  ·
    refine ⟨122206731681828855141240407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81471154454552570094160271 122206731681828855141240407)
    ·
      refine ⟨183310097522743282711860611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122206731681828855141240407 183310097522743282711860611)
      ·
        refine ⟨274965146284114924067790917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183310097522743282711860611 274965146284114924067790917)
        ·
          refine ⟨51555964928271548262710797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 274965146284114924067790917 51555964928271548262710797)
          ·
            refine ⟨19333486848101830598516549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51555964928271548262710797 19333486848101830598516549)
            ·
              refine ⟨3625028784019093237221853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19333486848101830598516549 3625028784019093237221853)
              ·
                refine ⟨1359385794007159963958195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3625028784019093237221853 1359385794007159963958195)
                ·
                  refine ⟨2039078691010739945937293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1359385794007159963958195 2039078691010739945937293)
                  ·
                    refine ⟨764654509129027479726485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2039078691010739945937293 764654509129027479726485)
                    ·
                      rfl

theorem cell22_2233739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 1, 3].length) (baseStart_2233739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233739 prefixEnd_2233739 := by exact prefixLift 2233739
  have htrace : WordTrace (prefixWord ++ tailWord_2233739) baseStart_2233739 baseEnd_2233739 := by
    simpa [prefixWord, tailWord_2233739, baseEnd_2233739] using wordTrace_append hprefix tailTrace_2233739
  have hstable : (prefixWord ++ tailWord_2233739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233739).length < 2 ^ (prefixWord ++ tailWord_2233739).sum := by decide
  have hdescent : baseEnd_2233739 < baseStart_2233739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233752 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 7]
def baseStart_2233752 : Nat := 118140960795 + 2233752 * 2 ^ 59
def prefixEnd_2233752 : Nat := 4983230072969 + 3 ^ 40 * 2233752 * 2
def baseEnd_2233752 : Nat := 254886319764899926383815

theorem tailTrace_2233752 : CollatzResearch.WordTrace tailWord_2233752 prefixEnd_2233752 254886319764899926383815 := by
  unfold tailWord_2233752
  simp only [CollatzResearch.WordTrace]
  refine ⟨40735814301752736657191755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54314419069003648876255673 40735814301752736657191755)
  ·
    refine ⟨61103721452629104985787633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40735814301752736657191755 61103721452629104985787633)
    ·
      refine ⟨45827791089471828739340725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61103721452629104985787633 45827791089471828739340725)
      ·
        refine ⟨4296355414637983944313193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45827791089471828739340725 4296355414637983944313193)
        ·
          refine ⟨3222266560978487958234895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4296355414637983944313193 3222266560978487958234895)
          ·
            refine ⟨4833399841467731937352343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3222266560978487958234895 4833399841467731937352343)
            ·
              refine ⟨7250099762201597906028515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4833399841467731937352343 7250099762201597906028515)
              ·
                refine ⟨10875149643302396859042773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7250099762201597906028515 10875149643302396859042773)
                ·
                  refine ⟨254886319764899926383815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10875149643302396859042773 254886319764899926383815)
                  ·
                    rfl

theorem cell22_2233752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 7].length) (baseStart_2233752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233752 prefixEnd_2233752 := by exact prefixLift 2233752
  have htrace : WordTrace (prefixWord ++ tailWord_2233752) baseStart_2233752 baseEnd_2233752 := by
    simpa [prefixWord, tailWord_2233752, baseEnd_2233752] using wordTrace_append hprefix tailTrace_2233752
  have hstable : (prefixWord ++ tailWord_2233752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233752).length < 2 ^ (prefixWord ++ tailWord_2233752).sum := by decide
  have hdescent : baseEnd_2233752 < baseStart_2233752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233756 : List Nat := [2, 2, 3, 4, 1, 1, 2, 1, 3, 3]
def baseStart_2233756 : Nat := 118140960795 + 2233756 * 2 ^ 59
def prefixEnd_2233756 : Nat := 4983230072969 + 3 ^ 40 * 2233756 * 2
def baseEnd_2233756 : Nat := 764660328576445102051433

theorem tailTrace_2233756 : CollatzResearch.WordTrace tailWord_2233756 prefixEnd_2233756 764660328576445102051433 := by
  unfold tailWord_2233756
  simp only [CollatzResearch.WordTrace]
  refine ⟨40735887247745490998764561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54314516330327321331686081 40735887247745490998764561)
  ·
    refine ⟨30551915435809118249073421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40735887247745490998764561 30551915435809118249073421)
    ·
      refine ⟨11456968288428419343402533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30551915435809118249073421 11456968288428419343402533)
      ·
        refine ⟨2148181554080328626887975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11456968288428419343402533 2148181554080328626887975)
        ·
          refine ⟨3222272331120492940331963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2148181554080328626887975 3222272331120492940331963)
          ·
            refine ⟨4833408496680739410497945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3222272331120492940331963 4833408496680739410497945)
            ·
              refine ⟨3625056372510554557873459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4833408496680739410497945 3625056372510554557873459)
              ·
                refine ⟨5437584558765831836810189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3625056372510554557873459 5437584558765831836810189)
                ·
                  refine ⟨2039094209537186938803821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5437584558765831836810189 2039094209537186938803821)
                  ·
                    refine ⟨764660328576445102051433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2039094209537186938803821 764660328576445102051433)
                    ·
                      rfl

theorem cell22_2233756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_2233756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233756 prefixEnd_2233756 := by exact prefixLift 2233756
  have htrace : WordTrace (prefixWord ++ tailWord_2233756) baseStart_2233756 baseEnd_2233756 := by
    simpa [prefixWord, tailWord_2233756, baseEnd_2233756] using wordTrace_append hprefix tailTrace_2233756
  have hstable : (prefixWord ++ tailWord_2233756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233756).length < 2 ^ (prefixWord ++ tailWord_2233756).sum := by decide
  have hdescent : baseEnd_2233756 < baseStart_2233756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233765 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 3, 4]
def baseStart_2233765 : Nat := 118140960795 + 2233765 * 2 ^ 59
def prefixEnd_2233765 : Nat := 4983230072969 + 3 ^ 40 * 2233765 * 2
def baseEnd_2233765 : Nat := 764663409460372078576405

theorem tailTrace_2233765 : CollatzResearch.WordTrace tailWord_2233765 prefixEnd_2233765 764663409460372078576405 := by
  unfold tailWord_2233765
  simp only [CollatzResearch.WordTrace]
  refine ⟨81472102752458376534606749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54314735168305584356404499 81472102752458376534606749)
  ·
    refine ⟨30552038532171891200477531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81472102752458376534606749 30552038532171891200477531)
    ·
      refine ⟨45828057798257836800716297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30552038532171891200477531 45828057798257836800716297)
      ·
        refine ⟨34371043348693377600537223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45828057798257836800716297 34371043348693377600537223)
        ·
          refine ⟨51556565023040066400805835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34371043348693377600537223 51556565023040066400805835)
          ·
            refine ⟨77334847534560099601208753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51556565023040066400805835 77334847534560099601208753)
            ·
              refine ⟨58001135650920074700906565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77334847534560099601208753 58001135650920074700906565)
              ·
                refine ⟨10875212934547514006419981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58001135650920074700906565 10875212934547514006419981)
                ·
                  refine ⟨4078204850455317752407493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10875212934547514006419981 4078204850455317752407493)
                  ·
                    refine ⟨764663409460372078576405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4078204850455317752407493 764663409460372078576405)
                    ·
                      rfl

theorem cell22_2233765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_2233765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233765 prefixEnd_2233765 := by exact prefixLift 2233765
  have htrace : WordTrace (prefixWord ++ tailWord_2233765) baseStart_2233765 baseEnd_2233765 := by
    simpa [prefixWord, tailWord_2233765, baseEnd_2233765] using wordTrace_append hprefix tailTrace_2233765
  have hstable : (prefixWord ++ tailWord_2233765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233765).length < 2 ^ (prefixWord ++ tailWord_2233765).sum := by decide
  have hdescent : baseEnd_2233765 < baseStart_2233765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233795 : List Nat := [1, 1, 1, 3, 1, 1, 4, 4, 1, 5]
def baseStart_2233795 : Nat := 118140960795 + 2233795 * 2 ^ 59
def prefixEnd_2233795 : Nat := 4983230072969 + 3 ^ 40 * 2233795 * 2
def baseEnd_2233795 : Nat := 764673679073462000326313

theorem tailTrace_2233795 : CollatzResearch.WordTrace tailWord_2233795 prefixEnd_2233795 764673679073462000326313 := by
  unfold tailWord_2233795
  simp only [CollatzResearch.WordTrace]
  refine ⟨81473196942349691658198839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54315464628233127772132559 81473196942349691658198839)
  ·
    refine ⟨122209795413524537487298259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81473196942349691658198839 122209795413524537487298259)
    ·
      refine ⟨183314693120286806230947389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122209795413524537487298259 183314693120286806230947389)
      ·
        refine ⟨68743009920107552336605271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183314693120286806230947389 68743009920107552336605271)
        ·
          refine ⟨103114514880161328504907907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68743009920107552336605271 103114514880161328504907907)
          ·
            refine ⟨154671772320241992757361861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103114514880161328504907907 154671772320241992757361861)
            ·
              refine ⟨29000957310045373642005349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154671772320241992757361861 29000957310045373642005349)
              ·
                refine ⟨5437679495633507557876003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29000957310045373642005349 5437679495633507557876003)
                ·
                  refine ⟨8156519243450261336814005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5437679495633507557876003 8156519243450261336814005)
                  ·
                    refine ⟨764673679073462000326313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8156519243450261336814005 764673679073462000326313)
                    ·
                      rfl

theorem cell22_2233795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 5].length) (baseStart_2233795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233795 prefixEnd_2233795 := by exact prefixLift 2233795
  have htrace : WordTrace (prefixWord ++ tailWord_2233795) baseStart_2233795 baseEnd_2233795 := by
    simpa [prefixWord, tailWord_2233795, baseEnd_2233795] using wordTrace_append hprefix tailTrace_2233795
  have hstable : (prefixWord ++ tailWord_2233795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233795).length < 2 ^ (prefixWord ++ tailWord_2233795).sum := by decide
  have hdescent : baseEnd_2233795 < baseStart_2233795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233814 : List Nat := [5, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_2233814 : Nat := 118140960795 + 2233814 * 2 ^ 59
def prefixEnd_2233814 : Nat := 4983230072969 + 3 ^ 40 * 2233814 * 2
def baseEnd_2233814 : Nat := 254893394387250761367085

theorem tailTrace_2233814 : CollatzResearch.WordTrace tailWord_2233814 prefixEnd_2233814 254893394387250761367085 := by
  unfold tailWord_2233814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5092118120580053618946281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54315926619520571935426997 5092118120580053618946281)
  ·
    refine ⟨3819088590435040214209711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5092118120580053618946281 3819088590435040214209711)
    ·
      refine ⟨5728632885652560321314567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3819088590435040214209711 5728632885652560321314567)
      ·
        refine ⟨8592949328478840481971851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5728632885652560321314567 8592949328478840481971851)
        ·
          refine ⟨12889423992718260722957777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8592949328478840481971851 12889423992718260722957777)
          ·
            refine ⟨9667067994538695542218333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12889423992718260722957777 9667067994538695542218333)
            ·
              refine ⟨3625150497952010828331875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9667067994538695542218333 3625150497952010828331875)
              ·
                refine ⟨5437725746928016242497813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3625150497952010828331875 5437725746928016242497813)
                ·
                  refine ⟨254893394387250761367085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5437725746928016242497813 254893394387250761367085)
                  ·
                    rfl

theorem cell22_2233814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_2233814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233814 prefixEnd_2233814 := by exact prefixLift 2233814
  have htrace : WordTrace (prefixWord ++ tailWord_2233814) baseStart_2233814 baseEnd_2233814 := by
    simpa [prefixWord, tailWord_2233814, baseEnd_2233814] using wordTrace_append hprefix tailTrace_2233814
  have hstable : (prefixWord ++ tailWord_2233814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233814).length < 2 ^ (prefixWord ++ tailWord_2233814).sum := by decide
  have hdescent : baseEnd_2233814 < baseStart_2233814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233825 : List Nat := [1, 2, 3, 1, 2, 3, 1, 9]
def baseStart_2233825 : Nat := 118140960795 + 2233825 * 2 ^ 59
def prefixEnd_2233825 : Nat := 4983230072969 + 3 ^ 40 * 2233825 * 2
def baseEnd_2233825 : Nat := 84964883187394658008469

theorem tailTrace_2233825 : CollatzResearch.WordTrace tailWord_2233825 prefixEnd_2233825 84964883187394658008469 := by
  unfold tailWord_2233825
  simp only [CollatzResearch.WordTrace]
  refine ⟨81474291132241006781790929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54316194088160671187860619 81474291132241006781790929)
  ·
    refine ⟨61105718349180755086343197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81474291132241006781790929 61105718349180755086343197)
    ·
      refine ⟨22914644380942783157378699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61105718349180755086343197 22914644380942783157378699)
      ·
        refine ⟨34371966571414174736068049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22914644380942783157378699 34371966571414174736068049)
        ·
          refine ⟨25778974928560631052051037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34371966571414174736068049 25778974928560631052051037)
          ·
            refine ⟨9667115598210236644519139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25778974928560631052051037 9667115598210236644519139)
            ·
              refine ⟨14500673397315354966778709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9667115598210236644519139 14500673397315354966778709)
              ·
                refine ⟨84964883187394658008469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14500673397315354966778709 84964883187394658008469)
                ·
                  rfl

theorem cell22_2233825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 9].length) (baseStart_2233825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233825 prefixEnd_2233825 := by exact prefixLift 2233825
  have htrace : WordTrace (prefixWord ++ tailWord_2233825) baseStart_2233825 baseEnd_2233825 := by
    simpa [prefixWord, tailWord_2233825, baseEnd_2233825] using wordTrace_append hprefix tailTrace_2233825
  have hstable : (prefixWord ++ tailWord_2233825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233825).length < 2 ^ (prefixWord ++ tailWord_2233825).sum := by decide
  have hdescent : baseEnd_2233825 < baseStart_2233825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233842 : List Nat := [3, 2, 1, 4, 1, 1, 2, 8]
def baseStart_2233842 : Nat := 118140960795 + 2233842 * 2 ^ 59
def prefixEnd_2233842 : Nat := 4983230072969 + 3 ^ 40 * 2233842 * 2
def baseEnd_2233842 : Nat := 84965529792663282711241

theorem tailTrace_2233842 : CollatzResearch.WordTrace tailWord_2233842 prefixEnd_2233842 84965529792663282711241 := by
  unfold tailWord_2233842
  simp only [CollatzResearch.WordTrace]
  refine ⟨20368727793294854671289945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54316607448786279123439853 20368727793294854671289945)
  ·
    refine ⟨15276545844971141003467459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20368727793294854671289945 15276545844971141003467459)
    ·
      refine ⟨22914818767456711505201189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15276545844971141003467459 22914818767456711505201189)
      ·
        refine ⟨4296528518898133407225223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22914818767456711505201189 4296528518898133407225223)
        ·
          refine ⟨6444792778347200110837835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4296528518898133407225223 6444792778347200110837835)
          ·
            refine ⟨9667189167520800166256753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6444792778347200110837835 9667189167520800166256753)
            ·
              refine ⟨7250391875640600124692565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9667189167520800166256753 7250391875640600124692565)
              ·
                refine ⟨84965529792663282711241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7250391875640600124692565 84965529792663282711241)
                ·
                  rfl

theorem cell22_2233842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 8].length) (baseStart_2233842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233842 prefixEnd_2233842 := by exact prefixLift 2233842
  have htrace : WordTrace (prefixWord ++ tailWord_2233842) baseStart_2233842 baseEnd_2233842 := by
    simpa [prefixWord, tailWord_2233842, baseEnd_2233842] using wordTrace_append hprefix tailTrace_2233842
  have hstable : (prefixWord ++ tailWord_2233842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233842).length < 2 ^ (prefixWord ++ tailWord_2233842).sum := by decide
  have hdescent : baseEnd_2233842 < baseStart_2233842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233876 : List Nat := [2, 4, 3, 1, 2, 2, 1, 7]
def baseStart_2233876 : Nat := 118140960795 + 2233876 * 2 ^ 59
def prefixEnd_2233876 : Nat := 4983230072969 + 3 ^ 40 * 2233876 * 2
def baseEnd_2233876 : Nat := 84966823003200532116785

theorem tailTrace_2233876 : CollatzResearch.WordTrace tailWord_2233876 prefixEnd_2233876 84966823003200532116785 := by
  unfold tailWord_2233876
  simp only [CollatzResearch.WordTrace]
  refine ⟨40738075627528121245948741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54317434170037494994598321 40738075627528121245948741)
  ·
    refine ⟨7638389180161522733615389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40738075627528121245948741 7638389180161522733615389)
    ·
      refine ⟨2864395942560571025105771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7638389180161522733615389 2864395942560571025105771)
      ·
        refine ⟨4296593913840856537658657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2864395942560571025105771 4296593913840856537658657)
        ·
          refine ⟨3222445435380642403243993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4296593913840856537658657 3222445435380642403243993)
          ·
            refine ⟨2416834076535481802432995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3222445435380642403243993 2416834076535481802432995)
            ·
              refine ⟨3625251114803222703649493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2416834076535481802432995 3625251114803222703649493)
              ·
                refine ⟨84966823003200532116785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3625251114803222703649493 84966823003200532116785)
                ·
                  rfl

theorem cell22_2233876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 7].length) (baseStart_2233876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233876 prefixEnd_2233876 := by exact prefixLift 2233876
  have htrace : WordTrace (prefixWord ++ tailWord_2233876) baseStart_2233876 baseEnd_2233876 := by
    simpa [prefixWord, tailWord_2233876, baseEnd_2233876] using wordTrace_append hprefix tailTrace_2233876
  have hstable : (prefixWord ++ tailWord_2233876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233876).length < 2 ^ (prefixWord ++ tailWord_2233876).sum := by decide
  have hdescent : baseEnd_2233876 < baseStart_2233876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233887 : List Nat := [1, 1, 2, 4, 1, 1, 4, 3, 5]
def baseStart_2233887 : Nat := 118140960795 + 2233887 * 2 ^ 59
def prefixEnd_2233887 : Nat := 4983230072969 + 3 ^ 40 * 2233887 * 2
def baseEnd_2233887 : Nat := 254901724184534809008677

theorem tailTrace_2233887 : CollatzResearch.WordTrace tailWord_2233887 prefixEnd_2233887 254901724184534809008677 := by
  unfold tailWord_2233887
  simp only [CollatzResearch.WordTrace]
  refine ⟨81476552458016391370547915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54317701638677594247031943 81476552458016391370547915)
  ·
    refine ⟨122214828687024587055821873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81476552458016391370547915 122214828687024587055821873)
    ·
      refine ⟨91661121515268440291866405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122214828687024587055821873 91661121515268440291866405)
      ·
        refine ⟨17186460284112832554724951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91661121515268440291866405 17186460284112832554724951)
        ·
          refine ⟨25779690426169248832087427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17186460284112832554724951 25779690426169248832087427)
          ·
            refine ⟨38669535639253873248131141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25779690426169248832087427 38669535639253873248131141)
            ·
              refine ⟨7250537932360101234024589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38669535639253873248131141 7250537932360101234024589)
              ·
                refine ⟨2718951724635037962759221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7250537932360101234024589 2718951724635037962759221)
                ·
                  refine ⟨254901724184534809008677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2718951724635037962759221 254901724184534809008677)
                  ·
                    rfl

theorem cell22_2233887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 5].length) (baseStart_2233887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233887 prefixEnd_2233887 := by exact prefixLift 2233887
  have htrace : WordTrace (prefixWord ++ tailWord_2233887) baseStart_2233887 baseEnd_2233887 := by
    simpa [prefixWord, tailWord_2233887, baseEnd_2233887] using wordTrace_append hprefix tailTrace_2233887
  have hstable : (prefixWord ++ tailWord_2233887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233887).length < 2 ^ (prefixWord ++ tailWord_2233887).sum := by decide
  have hdescent : baseEnd_2233887 < baseStart_2233887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233932 : List Nat := [2, 2, 1, 3, 1, 3, 1, 3, 6]
def baseStart_2233932 : Nat := 118140960795 + 2233932 * 2 ^ 59
def prefixEnd_2233932 : Nat := 4983230072969 + 3 ^ 40 * 2233932 * 2
def baseEnd_2233932 : Nat := 254906858991079769883631

theorem tailTrace_2233932 : CollatzResearch.WordTrace tailWord_2233932 prefixEnd_2233932 254906858991079769883631 := by
  unfold tailWord_2233932
  simp only [CollatzResearch.WordTrace]
  refine ⟨40739096871426682027968025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54318795828568909370624033 40739096871426682027968025)
  ·
    refine ⟨30554322653570011520976019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40739096871426682027968025 30554322653570011520976019)
    ·
      refine ⟨45831483980355017281464029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30554322653570011520976019 45831483980355017281464029)
      ·
        refine ⟨17186806492633131480549011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45831483980355017281464029 17186806492633131480549011)
        ·
          refine ⟨25780209738949697220823517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17186806492633131480549011 25780209738949697220823517)
          ·
            refine ⟨9667578652106136457808819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25780209738949697220823517 9667578652106136457808819)
            ·
              refine ⟨14501367978159204686713229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9667578652106136457808819 14501367978159204686713229)
              ·
                refine ⟨5438012991809701757517461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14501367978159204686713229 5438012991809701757517461)
                ·
                  refine ⟨254906858991079769883631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5438012991809701757517461 254906858991079769883631)
                  ·
                    rfl

theorem cell22_2233932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_2233932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233932 prefixEnd_2233932 := by exact prefixLift 2233932
  have htrace : WordTrace (prefixWord ++ tailWord_2233932) baseStart_2233932 baseEnd_2233932 := by
    simpa [prefixWord, tailWord_2233932, baseEnd_2233932] using wordTrace_append hprefix tailTrace_2233932
  have hstable : (prefixWord ++ tailWord_2233932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233932).length < 2 ^ (prefixWord ++ tailWord_2233932).sum := by decide
  have hdescent : baseEnd_2233932 < baseStart_2233932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233994 : List Nat := [3, 1, 2, 3, 2, 2, 2, 7]
def baseStart_2233994 : Nat := 118140960795 + 2233994 * 2 ^ 59
def prefixEnd_2233994 : Nat := 4983230072969 + 3 ^ 40 * 2233994 * 2
def baseEnd_2233994 : Nat := 84971311204476868288967

theorem tailTrace_2233994 : CollatzResearch.WordTrace tailWord_2233994 prefixEnd_2233994 84971311204476868288967 := by
  unfold tailWord_2233994
  simp only [CollatzResearch.WordTrace]
  refine ⟨20370113767157187161173259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54320303379085832429795357 20370113767157187161173259)
  ·
    refine ⟨30555170650735780741759889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20370113767157187161173259 30555170650735780741759889)
    ·
      refine ⟨22916377988051835556319917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30555170650735780741759889 22916377988051835556319917)
      ·
        refine ⟨8593641745519438333619969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22916377988051835556319917 8593641745519438333619969)
        ·
          refine ⟨6445231309139578750214977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8593641745519438333619969 6445231309139578750214977)
          ·
            refine ⟨4833923481854684062661233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6445231309139578750214977 4833923481854684062661233)
            ·
              refine ⟨3625442611391013046995925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4833923481854684062661233 3625442611391013046995925)
              ·
                refine ⟨84971311204476868288967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3625442611391013046995925 84971311204476868288967)
                ·
                  rfl

theorem cell22_2233994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 7].length) (baseStart_2233994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233994 prefixEnd_2233994 := by exact prefixLift 2233994
  have htrace : WordTrace (prefixWord ++ tailWord_2233994) baseStart_2233994 baseEnd_2233994 := by
    simpa [prefixWord, tailWord_2233994, baseEnd_2233994] using wordTrace_append hprefix tailTrace_2233994
  have hstable : (prefixWord ++ tailWord_2233994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233994).length < 2 ^ (prefixWord ++ tailWord_2233994).sum := by decide
  have hdescent : baseEnd_2233994 < baseStart_2233994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2233998 : List Nat := [4, 1, 1, 3, 1, 2, 4, 1, 2, 3]
def baseStart_2233998 : Nat := 118140960795 + 2233998 * 2 ^ 59
def prefixEnd_2233998 : Nat := 4983230072969 + 3 ^ 40 * 2233998 * 2
def baseEnd_2233998 : Nat := 764743170122037137500691

theorem tailTrace_2233998 : CollatzResearch.WordTrace tailWord_2233998 prefixEnd_2233998 764743170122037137500691 := by
  unfold tailWord_2233998
  simp only [CollatzResearch.WordTrace]
  refine ⟨10185075120076782165979831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54320400640409504885225765 10185075120076782165979831)
  ·
    refine ⟨15277612680115173248969747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10185075120076782165979831 15277612680115173248969747)
    ·
      refine ⟨22916419020172759873454621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15277612680115173248969747 22916419020172759873454621)
      ·
        refine ⟨8593657132564784952545483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22916419020172759873454621 8593657132564784952545483)
        ·
          refine ⟨12890485698847177428818225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8593657132564784952545483 12890485698847177428818225)
          ·
            refine ⟨9667864274135383071613669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12890485698847177428818225 9667864274135383071613669)
            ·
              refine ⟨1812724551400384325927563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9667864274135383071613669 1812724551400384325927563)
              ·
                refine ⟨2719086827100576488891345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1812724551400384325927563 2719086827100576488891345)
                ·
                  refine ⟨2039315120325432366668509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2719086827100576488891345 2039315120325432366668509)
                  ·
                    refine ⟨764743170122037137500691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2039315120325432366668509 764743170122037137500691)
                    ·
                      rfl

theorem cell22_2233998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_2233998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2233998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2233998 prefixEnd_2233998 := by exact prefixLift 2233998
  have htrace : WordTrace (prefixWord ++ tailWord_2233998) baseStart_2233998 baseEnd_2233998 := by
    simpa [prefixWord, tailWord_2233998, baseEnd_2233998] using wordTrace_append hprefix tailTrace_2233998
  have hstable : (prefixWord ++ tailWord_2233998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2233998).length < 2 ^ (prefixWord ++ tailWord_2233998).sum := by decide
  have hdescent : baseEnd_2233998 < baseStart_2233998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2233998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234039 : List Nat := [1, 1, 3, 1, 5, 1, 1, 4, 5]
def baseStart_2234039 : Nat := 118140960795 + 2234039 * 2 ^ 59
def prefixEnd_2234039 : Nat := 4983230072969 + 3 ^ 40 * 2234039 * 2
def baseEnd_2234039 : Nat := 254919068419975565741855

theorem tailTrace_2234039 : CollatzResearch.WordTrace tailWord_2234039 prefixEnd_2234039 254919068419975565741855 := by
  unfold tailWord_2234039
  simp only [CollatzResearch.WordTrace]
  refine ⟨81482096353465721330081171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54321397568977147553387447 81482096353465721330081171)
  ·
    refine ⟨122223144530198581995121757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81482096353465721330081171 122223144530198581995121757)
    ·
      refine ⟨45833679198824468248170659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122223144530198581995121757 45833679198824468248170659)
      ·
        refine ⟨68750518798236702372255989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45833679198824468248170659 68750518798236702372255989)
        ·
          refine ⟨6445361137334690847398999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68750518798236702372255989 6445361137334690847398999)
          ·
            refine ⟨9668041706002036271098499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6445361137334690847398999 9668041706002036271098499)
            ·
              refine ⟨14502062559003054406647749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9668041706002036271098499 14502062559003054406647749)
              ·
                refine ⟨2719136729813072701246453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14502062559003054406647749 2719136729813072701246453)
                ·
                  refine ⟨254919068419975565741855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2719136729813072701246453 254919068419975565741855)
                  ·
                    rfl

theorem cell22_2234039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 5].length) (baseStart_2234039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234039 prefixEnd_2234039 := by exact prefixLift 2234039
  have htrace : WordTrace (prefixWord ++ tailWord_2234039) baseStart_2234039 baseEnd_2234039 := by
    simpa [prefixWord, tailWord_2234039, baseEnd_2234039] using wordTrace_append hprefix tailTrace_2234039
  have hstable : (prefixWord ++ tailWord_2234039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234039).length < 2 ^ (prefixWord ++ tailWord_2234039).sum := by decide
  have hdescent : baseEnd_2234039 < baseStart_2234039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234077 : List Nat := [1, 4, 3, 3, 1, 1, 2, 3, 1, 3]
def baseStart_2234077 : Nat := 118140960795 + 2234077 * 2 ^ 59
def prefixEnd_2234077 : Nat := 4983230072969 + 3 ^ 40 * 2234077 * 2
def baseEnd_2234077 : Nat := 764770213436507264775449

theorem tailTrace_2234077 : CollatzResearch.WordTrace tailWord_2234077 prefixEnd_2234077 764770213436507264775449 := by
  unfold tailWord_2234077
  simp only [CollatzResearch.WordTrace]
  refine ⟨81483482327328053819964485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54322321551552035879976323 81483482327328053819964485)
  ·
    refine ⟨15278152936374010091243341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81483482327328053819964485 15278152936374010091243341)
    ·
      refine ⟨5729307351140253784216253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15278152936374010091243341 5729307351140253784216253)
      ·
        refine ⟨2148490256677595169081095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5729307351140253784216253 2148490256677595169081095)
        ·
          refine ⟨3222735385016392753621643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2148490256677595169081095 3222735385016392753621643)
          ·
            refine ⟨4834103077524589130432465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3222735385016392753621643 4834103077524589130432465)
            ·
              refine ⟨3625577308143441847824349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4834103077524589130432465 3625577308143441847824349)
              ·
                refine ⟨1359591490553790692934131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3625577308143441847824349 1359591490553790692934131)
                ·
                  refine ⟨2039387235830686039401197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1359591490553790692934131 2039387235830686039401197)
                  ·
                    refine ⟨764770213436507264775449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2039387235830686039401197 764770213436507264775449)
                    ·
                      rfl

theorem cell22_2234077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_2234077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234077 prefixEnd_2234077 := by exact prefixLift 2234077
  have htrace : WordTrace (prefixWord ++ tailWord_2234077) baseStart_2234077 baseEnd_2234077 := by
    simpa [prefixWord, tailWord_2234077, baseEnd_2234077] using wordTrace_append hprefix tailTrace_2234077
  have hstable : (prefixWord ++ tailWord_2234077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234077).length < 2 ^ (prefixWord ++ tailWord_2234077).sum := by decide
  have hdescent : baseEnd_2234077 < baseStart_2234077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234116 : List Nat := [2, 3, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_2234116 : Nat := 118140960795 + 2234116 * 2 ^ 59
def prefixEnd_2234116 : Nat := 4983230072969 + 3 ^ 40 * 2234116 * 2
def baseEnd_2234116 : Nat := 764783563933524163050329

theorem tailTrace_2234116 : CollatzResearch.WordTrace tailWord_2234116 prefixEnd_2234116 764783563933524163050329 := by
  unfold tailWord_2234116
  simp only [CollatzResearch.WordTrace]
  refine ⟨40742452387093381740317101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54323269849457842320422801 40742452387093381740317101)
  ·
    refine ⟨15278419645160018152618913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40742452387093381740317101 15278419645160018152618913)
    ·
      refine ⟨11458814733870013614464185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15278419645160018152618913 11458814733870013614464185)
      ·
        refine ⟨8594111050402510210848139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11458814733870013614464185 8594111050402510210848139)
        ·
          refine ⟨12891166575603765316272209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8594111050402510210848139 12891166575603765316272209)
          ·
            refine ⟨9668374931702823987204157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12891166575603765316272209 9668374931702823987204157)
            ·
              refine ⟨3625640599388558995201559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9668374931702823987204157 3625640599388558995201559)
              ·
                refine ⟨5438460899082838492802339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3625640599388558995201559 5438460899082838492802339)
                ·
                  refine ⟨8157691348624257739203509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5438460899082838492802339 8157691348624257739203509)
                  ·
                    refine ⟨764783563933524163050329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8157691348624257739203509 764783563933524163050329)
                    ·
                      rfl

theorem cell22_2234116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_2234116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234116 prefixEnd_2234116 := by exact prefixLift 2234116
  have htrace : WordTrace (prefixWord ++ tailWord_2234116) baseStart_2234116 baseEnd_2234116 := by
    simpa [prefixWord, tailWord_2234116, baseEnd_2234116] using wordTrace_append hprefix tailTrace_2234116
  have hstable : (prefixWord ++ tailWord_2234116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234116).length < 2 ^ (prefixWord ++ tailWord_2234116).sum := by decide
  have hdescent : baseEnd_2234116 < baseStart_2234116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234219 : List Nat := [1, 1, 1, 1, 2, 2, 3, 5, 6]
def baseStart_2234219 : Nat := 118140960795 + 2234219 * 2 ^ 59
def prefixEnd_2234219 : Nat := 4983230072969 + 3 ^ 40 * 2234219 * 2
def baseEnd_2234219 : Nat := 254939607646155409241671

theorem tailTrace_2234219 : CollatzResearch.WordTrace tailWord_2234219 prefixEnd_2234219 254939607646155409241671 := by
  unfold tailWord_2234219
  simp only [CollatzResearch.WordTrace]
  refine ⟨81488661492813612071633711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54325774328542408047755807 81488661492813612071633711)
  ·
    refine ⟨122232992239220418107450567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81488661492813612071633711 122232992239220418107450567)
    ·
      refine ⟨183349488358830627161175851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122232992239220418107450567 183349488358830627161175851)
      ·
        refine ⟨275024232538245940741763777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183349488358830627161175851 275024232538245940741763777)
        ·
          refine ⟨206268174403684455556322833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275024232538245940741763777 206268174403684455556322833)
          ·
            refine ⟨154701130802763341667242125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206268174403684455556322833 154701130802763341667242125)
            ·
              refine ⟨58012924051036253125215797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154701130802763341667242125 58012924051036253125215797)
              ·
                refine ⟨5438711629784648730488981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58012924051036253125215797 5438711629784648730488981)
                ·
                  refine ⟨254939607646155409241671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5438711629784648730488981 254939607646155409241671)
                  ·
                    rfl

theorem cell22_2234219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 6].length) (baseStart_2234219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234219 prefixEnd_2234219 := by exact prefixLift 2234219
  have htrace : WordTrace (prefixWord ++ tailWord_2234219) baseStart_2234219 baseEnd_2234219 := by
    simpa [prefixWord, tailWord_2234219, baseEnd_2234219] using wordTrace_append hprefix tailTrace_2234219
  have hstable : (prefixWord ++ tailWord_2234219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234219).length < 2 ^ (prefixWord ++ tailWord_2234219).sum := by decide
  have hdescent : baseEnd_2234219 < baseStart_2234219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234221 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_2234221 : Nat := 118140960795 + 2234221 * 2 ^ 59
def prefixEnd_2234221 : Nat := 4983230072969 + 3 ^ 40 * 2234221 * 2
def baseEnd_2234221 : Nat := 764819507579338889175007

theorem tailTrace_2234221 : CollatzResearch.WordTrace tailWord_2234221 prefixEnd_2234221 764819507579338889175007 := by
  unfold tailWord_2234221
  simp only [CollatzResearch.WordTrace]
  refine ⟨81488734438806366413206517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54325822959204244275471011 81488734438806366413206517)
  ·
    refine ⟨7639568853638096851238111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81488734438806366413206517 7639568853638096851238111)
    ·
      refine ⟨11459353280457145276857167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7639568853638096851238111 11459353280457145276857167)
      ·
        refine ⟨17189029920685717915285751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11459353280457145276857167 17189029920685717915285751)
        ·
          refine ⟨25783544881028576872928627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17189029920685717915285751 25783544881028576872928627)
          ·
            refine ⟨38675317321542865309392941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25783544881028576872928627 38675317321542865309392941)
            ·
              refine ⟨14503243995578574491022353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38675317321542865309392941 14503243995578574491022353)
              ·
                refine ⟨10877432996683930868266765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14503243995578574491022353 10877432996683930868266765)
                ·
                  refine ⟨4079037373756474075600037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10877432996683930868266765 4079037373756474075600037)
                  ·
                    refine ⟨764819507579338889175007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4079037373756474075600037 764819507579338889175007)
                    ·
                      rfl

theorem cell22_2234221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_2234221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234221 prefixEnd_2234221 := by exact prefixLift 2234221
  have htrace : WordTrace (prefixWord ++ tailWord_2234221) baseStart_2234221 baseEnd_2234221 := by
    simpa [prefixWord, tailWord_2234221, baseEnd_2234221] using wordTrace_append hprefix tailTrace_2234221
  have hstable : (prefixWord ++ tailWord_2234221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234221).length < 2 ^ (prefixWord ++ tailWord_2234221).sum := by decide
  have hdescent : baseEnd_2234221 < baseStart_2234221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234251 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 4, 3]
def baseStart_2234251 : Nat := 118140960795 + 2234251 * 2 ^ 59
def prefixEnd_2234251 : Nat := 4983230072969 + 3 ^ 40 * 2234251 * 2
def baseEnd_2234251 : Nat := 764829777192428810924915

theorem tailTrace_2234251 : CollatzResearch.WordTrace tailWord_2234251 prefixEnd_2234251 764829777192428810924915 := by
  unfold tailWord_2234251
  simp only [CollatzResearch.WordTrace]
  refine ⟨81489828628697681536798607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54326552419131787691199071 81489828628697681536798607)
  ·
    refine ⟨122234742943046522305197911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81489828628697681536798607 122234742943046522305197911)
    ·
      refine ⟨183352114414569783457796867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122234742943046522305197911 183352114414569783457796867)
      ·
        refine ⟨275028171621854675186695301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183352114414569783457796867 275028171621854675186695301)
        ·
          refine ⟨51567782179097751597505369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 275028171621854675186695301 51567782179097751597505369)
          ·
            refine ⟨38675836634323313698129027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51567782179097751597505369 38675836634323313698129027)
            ·
              refine ⟨58013754951484970547193541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38675836634323313698129027 58013754951484970547193541)
              ·
                refine ⟨10877579053403431977598789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58013754951484970547193541 10877579053403431977598789)
                ·
                  refine ⟨2039546072513143495799773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10877579053403431977598789 2039546072513143495799773)
                  ·
                    refine ⟨764829777192428810924915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2039546072513143495799773 764829777192428810924915)
                    ·
                      rfl

theorem cell22_2234251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 3].length) (baseStart_2234251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234251 prefixEnd_2234251 := by exact prefixLift 2234251
  have htrace : WordTrace (prefixWord ++ tailWord_2234251) baseStart_2234251 baseEnd_2234251 := by
    simpa [prefixWord, tailWord_2234251, baseEnd_2234251] using wordTrace_append hprefix tailTrace_2234251
  have hstable : (prefixWord ++ tailWord_2234251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234251).length < 2 ^ (prefixWord ++ tailWord_2234251).sum := by decide
  have hdescent : baseEnd_2234251 < baseStart_2234251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234332 : List Nat := [2, 2, 6, 1, 1, 1, 2, 7]
def baseStart_2234332 : Nat := 118140960795 + 2234332 * 2 ^ 59
def prefixEnd_2234332 : Nat := 4983230072969 + 3 ^ 40 * 2234332 * 2
def baseEnd_2234332 : Nat := 84984167238641288849963

theorem tailTrace_2234332 : CollatzResearch.WordTrace tailWord_2234332 prefixEnd_2234332 84984167238641288849963 := by
  unfold tailWord_2234332
  simp only [CollatzResearch.WordTrace]
  refine ⟨40746391470702116185248625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54328521960936154913664833 40746391470702116185248625)
  ·
    refine ⟨30559793603026587138936469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40746391470702116185248625 30559793603026587138936469)
    ·
      refine ⟨1432490325141871272137647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30559793603026587138936469 1432490325141871272137647)
      ·
        refine ⟨2148735487712806908206471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1432490325141871272137647 2148735487712806908206471)
        ·
          refine ⟨3223103231569210362309707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2148735487712806908206471 3223103231569210362309707)
          ·
            refine ⟨4834654847353815543464561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3223103231569210362309707 4834654847353815543464561)
            ·
              refine ⟨3625991135515361657598421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4834654847353815543464561 3625991135515361657598421)
              ·
                refine ⟨84984167238641288849963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3625991135515361657598421 84984167238641288849963)
                ·
                  rfl

theorem cell22_2234332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 7].length) (baseStart_2234332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234332 prefixEnd_2234332 := by exact prefixLift 2234332
  have htrace : WordTrace (prefixWord ++ tailWord_2234332) baseStart_2234332 baseEnd_2234332 := by
    simpa [prefixWord, tailWord_2234332, baseEnd_2234332] using wordTrace_append hprefix tailTrace_2234332
  have hstable : (prefixWord ++ tailWord_2234332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234332).length < 2 ^ (prefixWord ++ tailWord_2234332).sum := by decide
  have hdescent : baseEnd_2234332 < baseStart_2234332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234403 : List Nat := [1, 1, 1, 4, 3, 1, 4, 1, 1, 5]
def baseStart_2234403 : Nat := 118140960795 + 2234403 * 2 ^ 59
def prefixEnd_2234403 : Nat := 4983230072969 + 3 ^ 40 * 2234403 * 2
def baseEnd_2234403 : Nat := 764881809898751081124449

theorem tailTrace_2234403 : CollatzResearch.WordTrace tailWord_2234403 prefixEnd_2234403 764881809898751081124449 := by
  unfold tailWord_2234403
  simp only [CollatzResearch.WordTrace]
  refine ⟨81495372524147011496331863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54330248349431340997554575 81495372524147011496331863)
  ·
    refine ⟨122243058786220517244497795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81495372524147011496331863 122243058786220517244497795)
    ·
      refine ⟨183364588179330775866746693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122243058786220517244497795 183364588179330775866746693)
      ·
        refine ⟨34380860283624520475015005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183364588179330775866746693 34380860283624520475015005)
        ·
          refine ⟨12892822606359195178130627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34380860283624520475015005 12892822606359195178130627)
          ·
            refine ⟨19339233909538792767195941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12892822606359195178130627 19339233909538792767195941)
            ·
              refine ⟨3626106358038523643849239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19339233909538792767195941 3626106358038523643849239)
              ·
                refine ⟨5439159537057785465773859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3626106358038523643849239 5439159537057785465773859)
                ·
                  refine ⟨8158739305586678198660789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5439159537057785465773859 8158739305586678198660789)
                  ·
                    refine ⟨764881809898751081124449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8158739305586678198660789 764881809898751081124449)
                    ·
                      rfl

theorem cell22_2234403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 5].length) (baseStart_2234403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234403 prefixEnd_2234403 := by exact prefixLift 2234403
  have htrace : WordTrace (prefixWord ++ tailWord_2234403) baseStart_2234403 baseEnd_2234403 := by
    simpa [prefixWord, tailWord_2234403, baseEnd_2234403] using wordTrace_append hprefix tailTrace_2234403
  have hstable : (prefixWord ++ tailWord_2234403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234403).length < 2 ^ (prefixWord ++ tailWord_2234403).sum := by decide
  have hdescent : baseEnd_2234403 < baseStart_2234403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234418 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_2234418 : Nat := 118140960795 + 2234418 * 2 ^ 59
def prefixEnd_2234418 : Nat := 4983230072969 + 3 ^ 40 * 2234418 * 2
def baseEnd_2234418 : Nat := 764886944705296041999403

theorem tailTrace_2234418 : CollatzResearch.WordTrace tailWord_2234418 prefixEnd_2234418 764886944705296041999403 := by
  unfold tailWord_2234418
  simp only [CollatzResearch.WordTrace]
  refine ⟨20373979904773167264531977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54330613079395112705418605 20373979904773167264531977)
  ·
    refine ⟨15280484928579875448398983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20373979904773167264531977 15280484928579875448398983)
    ·
      refine ⟨22920727392869813172598475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15280484928579875448398983 22920727392869813172598475)
      ·
        refine ⟨34381091089304719758897713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22920727392869813172598475 34381091089304719758897713)
        ·
          refine ⟨25785818316978539819173285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34381091089304719758897713 25785818316978539819173285)
          ·
            refine ⟨4834840934433476216094991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25785818316978539819173285 4834840934433476216094991)
            ·
              refine ⟨7252261401650214324142487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4834840934433476216094991 7252261401650214324142487)
              ·
                refine ⟨10878392102475321486213731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7252261401650214324142487 10878392102475321486213731)
                ·
                  refine ⟨16317588153712982229320597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10878392102475321486213731 16317588153712982229320597)
                  ·
                    refine ⟨764886944705296041999403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16317588153712982229320597 764886944705296041999403)
                    ·
                      rfl

theorem cell22_2234418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_2234418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234418 prefixEnd_2234418 := by exact prefixLift 2234418
  have htrace : WordTrace (prefixWord ++ tailWord_2234418) baseStart_2234418 baseEnd_2234418 := by
    simpa [prefixWord, tailWord_2234418, baseEnd_2234418] using wordTrace_append hprefix tailTrace_2234418
  have hstable : (prefixWord ++ tailWord_2234418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234418).length < 2 ^ (prefixWord ++ tailWord_2234418).sum := by decide
  have hdescent : baseEnd_2234418 < baseStart_2234418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234422 : List Nat := [5, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_2234422 : Nat := 118140960795 + 2234422 * 2 ^ 59
def prefixEnd_2234422 : Nat := 4983230072969 + 3 ^ 40 * 2234422 * 2
def baseEnd_2234422 : Nat := 254962771329013788299797

theorem tailTrace_2234422 : CollatzResearch.WordTrace tailWord_2234422 prefixEnd_2234422 254962771329013788299797 := by
  unfold tailWord_2234422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5093504094442386108829595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54330710340718785160849013 5093504094442386108829595)
  ·
    refine ⟨7640256141663579163244393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5093504094442386108829595 7640256141663579163244393)
    ·
      refine ⟨5730192106247684372433295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7640256141663579163244393 5730192106247684372433295)
      ·
        refine ⟨8595288159371526558649943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5730192106247684372433295 8595288159371526558649943)
        ·
          refine ⟨12892932239057289837974915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8595288159371526558649943 12892932239057289837974915)
          ·
            refine ⟨19339398358585934756962373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12892932239057289837974915 19339398358585934756962373)
            ·
              refine ⟨3626137192234862766930445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19339398358585934756962373 3626137192234862766930445)
              ·
                refine ⟨1359801447088073537598917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3626137192234862766930445 1359801447088073537598917)
                ·
                  refine ⟨254962771329013788299797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1359801447088073537598917 254962771329013788299797)
                  ·
                    rfl

theorem cell22_2234422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_2234422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234422 prefixEnd_2234422 := by exact prefixLift 2234422
  have htrace : WordTrace (prefixWord ++ tailWord_2234422) baseStart_2234422 baseEnd_2234422 := by
    simpa [prefixWord, tailWord_2234422, baseEnd_2234422] using wordTrace_append hprefix tailTrace_2234422
  have hstable : (prefixWord ++ tailWord_2234422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234422).length < 2 ^ (prefixWord ++ tailWord_2234422).sum := by decide
  have hdescent : baseEnd_2234422 < baseStart_2234422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234424 : List Nat := [2, 1, 2, 1, 7, 1, 2, 1, 1, 4]
def baseStart_2234424 : Nat := 118140960795 + 2234424 * 2 ^ 59
def prefixEnd_2234424 : Nat := 4983230072969 + 3 ^ 40 * 2234424 * 2
def baseEnd_2234424 : Nat := 764888998627914026349385

theorem tailTrace_2234424 : CollatzResearch.WordTrace tailWord_2234424 prefixEnd_2234424 764888998627914026349385 := by
  unfold tailWord_2234424
  simp only [CollatzResearch.WordTrace]
  refine ⟨40748069228535466041423163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54330758971380621388564217 40748069228535466041423163)
  ·
    refine ⟨61122103842803199062134745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40748069228535466041423163 61122103842803199062134745)
    ·
      refine ⟨45841577882102399296601059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61122103842803199062134745 45841577882102399296601059)
      ·
        refine ⟨68762366823153598944901589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45841577882102399296601059 68762366823153598944901589)
        ·
          refine ⟨1611617972417662475271131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 68762366823153598944901589 1611617972417662475271131)
          ·
            refine ⟨2417426958626493712906697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1611617972417662475271131 2417426958626493712906697)
            ·
              refine ⟨1813070218969870284680023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2417426958626493712906697 1813070218969870284680023)
              ·
                refine ⟨2719605328454805427020035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1813070218969870284680023 2719605328454805427020035)
                ·
                  refine ⟨4079407992682208140530053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2719605328454805427020035 4079407992682208140530053)
                  ·
                    refine ⟨764888998627914026349385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4079407992682208140530053 764888998627914026349385)
                    ·
                      rfl

theorem cell22_2234424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 1, 4].length) (baseStart_2234424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234424 prefixEnd_2234424 := by exact prefixLift 2234424
  have htrace : WordTrace (prefixWord ++ tailWord_2234424) baseStart_2234424 baseEnd_2234424 := by
    simpa [prefixWord, tailWord_2234424, baseEnd_2234424] using wordTrace_append hprefix tailTrace_2234424
  have hstable : (prefixWord ++ tailWord_2234424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234424).length < 2 ^ (prefixWord ++ tailWord_2234424).sum := by decide
  have hdescent : baseEnd_2234424 < baseStart_2234424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234433 : List Nat := [1, 2, 5, 1, 2, 2, 9]
def baseStart_2234433 : Nat := 118140960795 + 2234433 * 2 ^ 59
def prefixEnd_2234433 : Nat := 4983230072969 + 3 ^ 40 * 2234433 * 2
def baseEnd_2234433 : Nat := 28329336278216333439791

theorem tailTrace_2234433 : CollatzResearch.WordTrace tailWord_2234433 prefixEnd_2234433 28329336278216333439791 := by
  unfold tailWord_2234433
  simp only [CollatzResearch.WordTrace]
  refine ⟨81496466714038326619923953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54330977809358884413282635 81496466714038326619923953)
  ·
    refine ⟨61122350035528744964942965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81496466714038326619923953 61122350035528744964942965)
    ·
      refine ⟨5730220315830819840463403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61122350035528744964942965 5730220315830819840463403)
      ·
        refine ⟨8595330473746229760695105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5730220315830819840463403 8595330473746229760695105)
        ·
          refine ⟨6446497855309672320521329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8595330473746229760695105 6446497855309672320521329)
          ·
            refine ⟨4834873391482254240390997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6446497855309672320521329 4834873391482254240390997)
            ·
              refine ⟨28329336278216333439791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4834873391482254240390997 28329336278216333439791)
              ·
                rfl

theorem cell22_2234433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 9].length) (baseStart_2234433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234433 prefixEnd_2234433 := by exact prefixLift 2234433
  have htrace : WordTrace (prefixWord ++ tailWord_2234433) baseStart_2234433 baseEnd_2234433 := by
    simpa [prefixWord, tailWord_2234433, baseEnd_2234433] using wordTrace_append hprefix tailTrace_2234433
  have hstable : (prefixWord ++ tailWord_2234433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234433).length < 2 ^ (prefixWord ++ tailWord_2234433).sum := by decide
  have hdescent : baseEnd_2234433 < baseStart_2234433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234454 : List Nat := [5, 2, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_2234454 : Nat := 118140960795 + 2234454 * 2 ^ 59
def prefixEnd_2234454 : Nat := 4983230072969 + 3 ^ 40 * 2234454 * 2
def baseEnd_2234454 : Nat := 764899268241003948099293

theorem tailTrace_2234454 : CollatzResearch.WordTrace tailWord_2234454 prefixEnd_2234454 764899268241003948099293 := by
  unfold tailWord_2234454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5093577040435140450402401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54331488431308164804292277 5093577040435140450402401)
  ·
    refine ⟨3820182780326355337801801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5093577040435140450402401 3820182780326355337801801)
    ·
      refine ⟨2865137085244766503351351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3820182780326355337801801 2865137085244766503351351)
      ·
        refine ⟨4297705627867149755027027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2865137085244766503351351 4297705627867149755027027)
        ·
          refine ⟨6446558441800724632540541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4297705627867149755027027 6446558441800724632540541)
          ·
            refine ⟨2417459415675271737202703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6446558441800724632540541 2417459415675271737202703)
            ·
              refine ⟨3626189123512907605804055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2417459415675271737202703 3626189123512907605804055)
              ·
                refine ⟨5439283685269361408706083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3626189123512907605804055 5439283685269361408706083)
                ·
                  refine ⟨8158925527904042113059125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5439283685269361408706083 8158925527904042113059125)
                  ·
                    refine ⟨764899268241003948099293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8158925527904042113059125 764899268241003948099293)
                    ·
                      rfl

theorem cell22_2234454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_2234454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234454 prefixEnd_2234454 := by exact prefixLift 2234454
  have htrace : WordTrace (prefixWord ++ tailWord_2234454) baseStart_2234454 baseEnd_2234454 := by
    simpa [prefixWord, tailWord_2234454, baseEnd_2234454] using wordTrace_append hprefix tailTrace_2234454
  have hstable : (prefixWord ++ tailWord_2234454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234454).length < 2 ^ (prefixWord ++ tailWord_2234454).sum := by decide
  have hdescent : baseEnd_2234454 < baseStart_2234454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234478 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 9]
def baseStart_2234478 : Nat := 118140960795 + 2234478 * 2 ^ 59
def prefixEnd_2234478 : Nat := 4983230072969 + 3 ^ 40 * 2234478 * 2
def baseEnd_2234478 : Nat := 254969161310491961833073

theorem tailTrace_2234478 : CollatzResearch.WordTrace tailWord_2234478 prefixEnd_2234478 254969161310491961833073 := by
  unfold tailWord_2234478
  simp only [CollatzResearch.WordTrace]
  refine ⟨10187263499859412413164011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54332071999250199536874725 10187263499859412413164011)
  ·
    refine ⟨15280895249789118619746017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10187263499859412413164011 15280895249789118619746017)
    ·
      refine ⟨11460671437341838964809513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15280895249789118619746017 11460671437341838964809513)
      ·
        refine ⟨8595503578006379223607135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11460671437341838964809513 8595503578006379223607135)
        ·
          refine ⟨12893255367009568835410703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8595503578006379223607135 12893255367009568835410703)
          ·
            refine ⟨19339883050514353253116055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12893255367009568835410703 19339883050514353253116055)
            ·
              refine ⟨29009824575771529879674083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19339883050514353253116055 29009824575771529879674083)
              ·
                refine ⟨43514736863657294819511125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29009824575771529879674083 43514736863657294819511125)
                ·
                  refine ⟨254969161310491961833073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43514736863657294819511125 254969161310491961833073)
                  ·
                    rfl

theorem cell22_2234478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_2234478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234478 prefixEnd_2234478 := by exact prefixLift 2234478
  have htrace : WordTrace (prefixWord ++ tailWord_2234478) baseStart_2234478 baseEnd_2234478 := by
    simpa [prefixWord, tailWord_2234478, baseEnd_2234478] using wordTrace_append hprefix tailTrace_2234478
  have hstable : (prefixWord ++ tailWord_2234478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234478).length < 2 ^ (prefixWord ++ tailWord_2234478).sum := by decide
  have hdescent : baseEnd_2234478 < baseStart_2234478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234499 : List Nat := [1, 1, 1, 3, 3, 4, 3, 2, 1, 3]
def baseStart_2234499 : Nat := 118140960795 + 2234499 * 2 ^ 59
def prefixEnd_2234499 : Nat := 4983230072969 + 3 ^ 40 * 2234499 * 2
def baseEnd_2234499 : Nat := 764914672660638830724155

theorem tailTrace_2234499 : CollatzResearch.WordTrace tailWord_2234499 prefixEnd_2234499 764914672660638830724155 := by
  unfold tailWord_2234499
  simp only [CollatzResearch.WordTrace]
  refine ⟨81498873931799219891826551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54332582621199479927884367 81498873931799219891826551)
  ·
    refine ⟨122248310897698829837739827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81498873931799219891826551 122248310897698829837739827)
    ·
      refine ⟨183372466346548244756609741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122248310897698829837739827 183372466346548244756609741)
      ·
        refine ⟨68764674879955591783728653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183372466346548244756609741 68764674879955591783728653)
        ·
          refine ⟨25786753079983346918898245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68764674879955591783728653 25786753079983346918898245)
          ·
            refine ⟨4835016202496877547293421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25786753079983346918898245 4835016202496877547293421)
            ·
              refine ⟨1813131075936329080235033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4835016202496877547293421 1813131075936329080235033)
              ·
                refine ⟨1359848306952246810176275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1813131075936329080235033 1359848306952246810176275)
                ·
                  refine ⟨2039772460428370215264413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1359848306952246810176275 2039772460428370215264413)
                  ·
                    refine ⟨764914672660638830724155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2039772460428370215264413 764914672660638830724155)
                    ·
                      rfl

theorem cell22_2234499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 1, 3].length) (baseStart_2234499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234499 prefixEnd_2234499 := by exact prefixLift 2234499
  have htrace : WordTrace (prefixWord ++ tailWord_2234499) baseStart_2234499 baseEnd_2234499 := by
    simpa [prefixWord, tailWord_2234499, baseEnd_2234499] using wordTrace_append hprefix tailTrace_2234499
  have hstable : (prefixWord ++ tailWord_2234499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234499).length < 2 ^ (prefixWord ++ tailWord_2234499).sum := by decide
  have hdescent : baseEnd_2234499 < baseStart_2234499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234525 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_2234525 : Nat := 118140960795 + 2234525 * 2 ^ 59
def prefixEnd_2234525 : Nat := 4983230072969 + 3 ^ 40 * 2234525 * 2
def baseEnd_2234525 : Nat := 764923572991983429574075

theorem tailTrace_2234525 : CollatzResearch.WordTrace tailWord_2234525 prefixEnd_2234525 764923572991983429574075 := by
  unfold tailWord_2234525
  simp only [CollatzResearch.WordTrace]
  refine ⟨81499822229705026332273029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54333214819803350888182019 81499822229705026332273029)
  ·
    refine ⟨15281216668069692437301193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81499822229705026332273029 15281216668069692437301193)
    ·
      refine ⟨11460912501052269327975895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15281216668069692437301193 11460912501052269327975895)
      ·
        refine ⟨17191368751578403991963843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11460912501052269327975895 17191368751578403991963843)
        ·
          refine ⟨25787053127367605987945765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17191368751578403991963843 25787053127367605987945765)
          ·
            refine ⟨4835072461381426122739831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25787053127367605987945765 4835072461381426122739831)
            ·
              refine ⟨7252608692072139184109747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4835072461381426122739831 7252608692072139184109747)
              ·
                refine ⟨10878913038108208776164621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7252608692072139184109747 10878913038108208776164621)
                ·
                  refine ⟨4079592389290578291061733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10878913038108208776164621 4079592389290578291061733)
                  ·
                    refine ⟨764923572991983429574075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4079592389290578291061733 764923572991983429574075)
                    ·
                      rfl

theorem cell22_2234525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_2234525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234525 prefixEnd_2234525 := by exact prefixLift 2234525
  have htrace : WordTrace (prefixWord ++ tailWord_2234525) baseStart_2234525 baseEnd_2234525 := by
    simpa [prefixWord, tailWord_2234525, baseEnd_2234525] using wordTrace_append hprefix tailTrace_2234525
  have hstable : (prefixWord ++ tailWord_2234525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234525).length < 2 ^ (prefixWord ++ tailWord_2234525).sum := by decide
  have hdescent : baseEnd_2234525 < baseStart_2234525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234643 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 2, 8]
def baseStart_2234643 : Nat := 118140960795 + 2234643 * 2 ^ 59
def prefixEnd_2234643 : Nat := 4983230072969 + 3 ^ 40 * 2234643 * 2
def baseEnd_2234643 : Nat := 764963966803470455123713

theorem tailTrace_2234643 : CollatzResearch.WordTrace tailWord_2234643 prefixEnd_2234643 764963966803470455123713 := by
  unfold tailWord_2234643
  simp only [CollatzResearch.WordTrace]
  refine ⟨81504126043277532485068583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54336084028851688323379055 81504126043277532485068583)
  ·
    refine ⟨122256189064916298727602875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81504126043277532485068583 122256189064916298727602875)
    ·
      refine ⟨183384283597374448091404313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122256189064916298727602875 183384283597374448091404313)
      ·
        refine ⟨137538212698030836068553235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183384283597374448091404313 137538212698030836068553235)
        ·
          refine ⟨206307319047046254102829853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137538212698030836068553235 206307319047046254102829853)
          ·
            refine ⟨77365244642642345288561195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206307319047046254102829853 77365244642642345288561195)
            ·
              refine ⟨116047866963963517932841793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77365244642642345288561195 116047866963963517932841793)
              ·
                refine ⟨87035900222972638449631345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116047866963963517932841793 87035900222972638449631345)
                ·
                  refine ⟨65276925167229478837223509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87035900222972638449631345 65276925167229478837223509)
                  ·
                    refine ⟨764963966803470455123713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65276925167229478837223509 764963966803470455123713)
                    ·
                      rfl

theorem cell22_2234643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 8].length) (baseStart_2234643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234643 prefixEnd_2234643 := by exact prefixLift 2234643
  have htrace : WordTrace (prefixWord ++ tailWord_2234643) baseStart_2234643 baseEnd_2234643 := by
    simpa [prefixWord, tailWord_2234643, baseEnd_2234643] using wordTrace_append hprefix tailTrace_2234643
  have hstable : (prefixWord ++ tailWord_2234643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234643).length < 2 ^ (prefixWord ++ tailWord_2234643).sum := by decide
  have hdescent : baseEnd_2234643 < baseStart_2234643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234720 : List Nat := [2, 1, 1, 3, 5, 10]
def baseStart_2234720 : Nat := 118140960795 + 2234720 * 2 ^ 59
def prefixEnd_2234720 : Nat := 4983230072969 + 3 ^ 40 * 2234720 * 2
def baseEnd_2234720 : Nat := 9444325005889727419117

theorem tailTrace_2234720 : CollatzResearch.WordTrace tailWord_2234720 prefixEnd_2234720 9444325005889727419117 := by
  unfold tailWord_2234720
  simp only [CollatzResearch.WordTrace]
  refine ⟨40753467231999287317810807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54337956309332383090414409 40753467231999287317810807)
  ·
    refine ⟨61130200847998930976716211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40753467231999287317810807 61130200847998930976716211)
    ·
      refine ⟨91695301271998396465074317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61130200847998930976716211 91695301271998396465074317)
      ·
        refine ⟨34385737976999398674402869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91695301271998396465074317 34385737976999398674402869)
        ·
          refine ⟨3223662935343693625725269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34385737976999398674402869 3223662935343693625725269)
          ·
            refine ⟨9444325005889727419117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3223662935343693625725269 9444325005889727419117)
            ·
              rfl

theorem cell22_2234720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 10].length) (baseStart_2234720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234720 prefixEnd_2234720 := by exact prefixLift 2234720
  have htrace : WordTrace (prefixWord ++ tailWord_2234720) baseStart_2234720 baseEnd_2234720 := by
    simpa [prefixWord, tailWord_2234720, baseEnd_2234720] using wordTrace_append hprefix tailTrace_2234720
  have hstable : (prefixWord ++ tailWord_2234720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234720).length < 2 ^ (prefixWord ++ tailWord_2234720).sum := by decide
  have hdescent : baseEnd_2234720 < baseStart_2234720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234724 : List Nat := [2, 3, 1, 1, 3, 1, 4, 2, 2, 3]
def baseStart_2234724 : Nat := 118140960795 + 2234724 * 2 ^ 59
def prefixEnd_2234724 : Nat := 4983230072969 + 3 ^ 40 * 2234724 * 2
def baseEnd_2234724 : Nat := 764991694758813243848465

theorem tailTrace_2234724 : CollatzResearch.WordTrace tailWord_2234724 prefixEnd_2234724 764991694758813243848465 := by
  unfold tailWord_2234724
  simp only [CollatzResearch.WordTrace]
  refine ⟨40753540177992041659383613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54338053570656055545844817 40753540177992041659383613)
  ·
    refine ⟨15282577566747015622268855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40753540177992041659383613 15282577566747015622268855)
    ·
      refine ⟨22923866350120523433403283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15282577566747015622268855 22923866350120523433403283)
      ·
        refine ⟨34385799525180785150104925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22923866350120523433403283 34385799525180785150104925)
        ·
          refine ⟨12894674821942794431289347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34385799525180785150104925 12894674821942794431289347)
          ·
            refine ⟨19342012232914191646934021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12894674821942794431289347 19342012232914191646934021)
            ·
              refine ⟨3626627293671410933800129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19342012232914191646934021 3626627293671410933800129)
              ·
                refine ⟨2719970470253558200350097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3626627293671410933800129 2719970470253558200350097)
                ·
                  refine ⟨2039977852690168650262573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2719970470253558200350097 2039977852690168650262573)
                  ·
                    refine ⟨764991694758813243848465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2039977852690168650262573 764991694758813243848465)
                    ·
                      rfl

theorem cell22_2234724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_2234724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234724 prefixEnd_2234724 := by exact prefixLift 2234724
  have htrace : WordTrace (prefixWord ++ tailWord_2234724) baseStart_2234724 baseEnd_2234724 := by
    simpa [prefixWord, tailWord_2234724, baseEnd_2234724] using wordTrace_append hprefix tailTrace_2234724
  have hstable : (prefixWord ++ tailWord_2234724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234724).length < 2 ^ (prefixWord ++ tailWord_2234724).sum := by decide
  have hdescent : baseEnd_2234724 < baseStart_2234724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234786 : List Nat := [3, 3, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_2234786 : Nat := 118140960795 + 2234786 * 2 ^ 59
def prefixEnd_2234786 : Nat := 4983230072969 + 3 ^ 40 * 2234786 * 2
def baseEnd_2234786 : Nat := 765012918625865748798275

theorem tailTrace_2234786 : CollatzResearch.WordTrace tailWord_2234786 prefixEnd_2234786 765012918625865748798275 := by
  unfold tailWord_2234786
  simp only [CollatzResearch.WordTrace]
  refine ⟨20377335420439866976881053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54339561121172978605016141 20377335420439866976881053)
  ·
    refine ⟨7641500782664950116330395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20377335420439866976881053 7641500782664950116330395)
    ·
      refine ⟨11462251173997425174495593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7641500782664950116330395 11462251173997425174495593)
      ·
        refine ⟨8596688380498068880871695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11462251173997425174495593 8596688380498068880871695)
        ·
          refine ⟨12895032570747103321307543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8596688380498068880871695 12895032570747103321307543)
          ·
            refine ⟨19342548856120654981961315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12895032570747103321307543 19342548856120654981961315)
            ·
              refine ⟨29013823284180982472941973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19342548856120654981961315 29013823284180982472941973)
              ·
                refine ⟨1360022966445983553419155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29013823284180982472941973 1360022966445983553419155)
                ·
                  refine ⟨2040034449668975330128733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360022966445983553419155 2040034449668975330128733)
                  ·
                    refine ⟨765012918625865748798275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2040034449668975330128733 765012918625865748798275)
                    ·
                      rfl

theorem cell22_2234786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_2234786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234786 prefixEnd_2234786 := by exact prefixLift 2234786
  have htrace : WordTrace (prefixWord ++ tailWord_2234786) baseStart_2234786 baseEnd_2234786 := by
    simpa [prefixWord, tailWord_2234786, baseEnd_2234786] using wordTrace_append hprefix tailTrace_2234786
  have hstable : (prefixWord ++ tailWord_2234786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234786).length < 2 ^ (prefixWord ++ tailWord_2234786).sum := by decide
  have hdescent : baseEnd_2234786 < baseStart_2234786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234820 : List Nat := [2, 3, 3, 2, 2, 2, 1, 3, 1, 3]
def baseStart_2234820 : Nat := 118140960795 + 2234820 * 2 ^ 59
def prefixEnd_2234820 : Nat := 4983230072969 + 3 ^ 40 * 2234820 * 2
def baseEnd_2234820 : Nat := 765024557520700993448171

theorem tailTrace_2234820 : CollatzResearch.WordTrace tailWord_2234820 prefixEnd_2234820 765024557520700993448171 := by
  unfold tailWord_2234820
  simp only [CollatzResearch.WordTrace]
  refine ⟨40755290881818145857130957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54340387842424194476174609 40755290881818145857130957)
  ·
    refine ⟨15283234080681804696424109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40755290881818145857130957 15283234080681804696424109)
    ·
      refine ⟨5731212780255676761159041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15283234080681804696424109 5731212780255676761159041)
      ·
        refine ⟨4298409585191757570869281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5731212780255676761159041 4298409585191757570869281)
        ·
          refine ⟨3223807188893818178151961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4298409585191757570869281 3223807188893818178151961)
          ·
            refine ⟨2417855391670363633613971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3223807188893818178151961 2417855391670363633613971)
            ·
              refine ⟨3626783087505545450420957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2417855391670363633613971 3626783087505545450420957)
              ·
                refine ⟨1360043657814579543907859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3626783087505545450420957 1360043657814579543907859)
                ·
                  refine ⟨2040065486721869315861789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360043657814579543907859 2040065486721869315861789)
                  ·
                    refine ⟨765024557520700993448171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2040065486721869315861789 765024557520700993448171)
                    ·
                      rfl

theorem cell22_2234820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_2234820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234820 prefixEnd_2234820 := by exact prefixLift 2234820
  have htrace : WordTrace (prefixWord ++ tailWord_2234820) baseStart_2234820 baseEnd_2234820 := by
    simpa [prefixWord, tailWord_2234820, baseEnd_2234820] using wordTrace_append hprefix tailTrace_2234820
  have hstable : (prefixWord ++ tailWord_2234820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234820).length < 2 ^ (prefixWord ++ tailWord_2234820).sum := by decide
  have hdescent : baseEnd_2234820 < baseStart_2234820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234850 : List Nat := [3, 3, 3, 2, 1, 2, 2, 1, 5]
def baseStart_2234850 : Nat := 118140960795 + 2234850 * 2 ^ 59
def prefixEnd_2234850 : Nat := 4983230072969 + 3 ^ 40 * 2234850 * 2
def baseEnd_2234850 : Nat := 255011609044596971732693

theorem tailTrace_2234850 : CollatzResearch.WordTrace tailWord_2234850 prefixEnd_2234850 255011609044596971732693 := by
  unfold tailWord_2234850
  simp only [CollatzResearch.WordTrace]
  refine ⟨20377918988381901709463501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54341117302351737891902669 20377918988381901709463501)
  ·
    refine ⟨7641719620643213141048813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20377918988381901709463501 7641719620643213141048813)
    ·
      refine ⟨2865644857741204927893305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7641719620643213141048813 2865644857741204927893305)
      ·
        refine ⟨2149233643305903695919979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2865644857741204927893305 2149233643305903695919979)
        ·
          refine ⟨3223850464958855543879969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2149233643305903695919979 3223850464958855543879969)
          ·
            refine ⟨2417887848719141657909977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3223850464958855543879969 2417887848719141657909977)
            ·
              refine ⟨1813415886539356243432483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2417887848719141657909977 1813415886539356243432483)
              ·
                refine ⟨2720123829809034365148725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1813415886539356243432483 2720123829809034365148725)
                ·
                  refine ⟨255011609044596971732693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2720123829809034365148725 255011609044596971732693)
                  ·
                    rfl

theorem cell22_2234850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_2234850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234850 prefixEnd_2234850 := by exact prefixLift 2234850
  have htrace : WordTrace (prefixWord ++ tailWord_2234850) baseStart_2234850 baseEnd_2234850 := by
    simpa [prefixWord, tailWord_2234850, baseEnd_2234850] using wordTrace_append hprefix tailTrace_2234850
  have hstable : (prefixWord ++ tailWord_2234850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234850).length < 2 ^ (prefixWord ++ tailWord_2234850).sum := by decide
  have hdescent : baseEnd_2234850 < baseStart_2234850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234859 : List Nat := [1, 1, 1, 1, 2, 3, 5, 3, 2, 3]
def baseStart_2234859 : Nat := 118140960795 + 2234859 * 2 ^ 59
def prefixEnd_2234859 : Nat := 4983230072969 + 3 ^ 40 * 2234859 * 2
def baseEnd_2234859 : Nat := 765037908017717891723051

theorem tailTrace_2234859 : CollatzResearch.WordTrace tailWord_2234859 prefixEnd_2234859 765037908017717891723051 := by
  unfold tailWord_2234859
  simp only [CollatzResearch.WordTrace]
  refine ⟨81512004210495001374931631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54341336140330000916621087 81512004210495001374931631)
  ·
    refine ⟨122268006315742502062397447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81512004210495001374931631 122268006315742502062397447)
    ·
      refine ⟨183402009473613753093596171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122268006315742502062397447 183402009473613753093596171)
      ·
        refine ⟨275103014210420629640394257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183402009473613753093596171 275103014210420629640394257)
        ·
          refine ⟨206327260657815472230295693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275103014210420629640394257 206327260657815472230295693)
          ·
            refine ⟨77372722746680802086360885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206327260657815472230295693 77372722746680802086360885)
            ·
              refine ⟨7253692757501325195596333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77372722746680802086360885 7253692757501325195596333)
              ·
                refine ⟨2720134784062996948348625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7253692757501325195596333 2720134784062996948348625)
                ·
                  refine ⟨2040101088047247711261469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2720134784062996948348625 2040101088047247711261469)
                  ·
                    refine ⟨765037908017717891723051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2040101088047247711261469 765037908017717891723051)
                    ·
                      rfl

theorem cell22_2234859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 3].length) (baseStart_2234859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234859 prefixEnd_2234859 := by exact prefixLift 2234859
  have htrace : WordTrace (prefixWord ++ tailWord_2234859) baseStart_2234859 baseEnd_2234859 := by
    simpa [prefixWord, tailWord_2234859, baseEnd_2234859] using wordTrace_append hprefix tailTrace_2234859
  have hstable : (prefixWord ++ tailWord_2234859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234859).length < 2 ^ (prefixWord ++ tailWord_2234859).sum := by decide
  have hdescent : baseEnd_2234859 < baseStart_2234859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234938 : List Nat := [3, 1, 1, 1, 3, 4, 2, 3, 1, 3]
def baseStart_2234938 : Nat := 118140960795 + 2234938 * 2 ^ 59
def prefixEnd_2234938 : Nat := 4983230072969 + 3 ^ 40 * 2234938 * 2
def baseEnd_2234938 : Nat := 765064951332188018997809

theorem tailTrace_2234938 : CollatzResearch.WordTrace tailWord_2234938 prefixEnd_2234938 765064951332188018997809 := by
  unfold tailWord_2234938
  simp only [CollatzResearch.WordTrace]
  refine ⟨20378721394302199466764367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54343257051472531911371645 20378721394302199466764367)
  ·
    refine ⟨30568082091453299200146551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20378721394302199466764367 30568082091453299200146551)
    ·
      refine ⟨45852123137179948800219827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30568082091453299200146551 45852123137179948800219827)
      ·
        refine ⟨68778184705769923200329741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45852123137179948800219827 68778184705769923200329741)
        ·
          refine ⟨25791819264663721200123653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68778184705769923200329741 25791819264663721200123653)
          ·
            refine ⟨4835966112124447725023185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25791819264663721200123653 4835966112124447725023185)
            ·
              refine ⟨3626974584093335793767389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4835966112124447725023185 3626974584093335793767389)
              ·
                refine ⟨1360115469035000922662771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3626974584093335793767389 1360115469035000922662771)
                ·
                  refine ⟨2040173203552501383994157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360115469035000922662771 2040173203552501383994157)
                  ·
                    refine ⟨765064951332188018997809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2040173203552501383994157 765064951332188018997809)
                    ·
                      rfl

theorem cell22_2234938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 1, 3].length) (baseStart_2234938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234938 prefixEnd_2234938 := by exact prefixLift 2234938
  have htrace : WordTrace (prefixWord ++ tailWord_2234938) baseStart_2234938 baseEnd_2234938 := by
    simpa [prefixWord, tailWord_2234938, baseEnd_2234938] using wordTrace_append hprefix tailTrace_2234938
  have hstable : (prefixWord ++ tailWord_2234938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234938).length < 2 ^ (prefixWord ++ tailWord_2234938).sum := by decide
  have hdescent : baseEnd_2234938 < baseStart_2234938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2234951 : List Nat := [1, 1, 4, 1, 4, 3, 1, 2, 5]
def baseStart_2234951 : Nat := 118140960795 + 2234951 * 2 ^ 59
def prefixEnd_2234951 : Nat := 4983230072969 + 3 ^ 40 * 2234951 * 2
def baseEnd_2234951 : Nat := 255023133832620106140923

theorem tailTrace_2234951 : CollatzResearch.WordTrace tailWord_2234951 prefixEnd_2234951 255023133832620106140923 := by
  unfold tailWord_2234951
  simp only [CollatzResearch.WordTrace]
  refine ⟨81515359726161701087280707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54343573150774467391520471 81515359726161701087280707)
  ·
    refine ⟨122273039589242551630921061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81515359726161701087280707 122273039589242551630921061)
    ·
      refine ⟨22926194922982978430797699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122273039589242551630921061 22926194922982978430797699)
      ·
        refine ⟨34389292384474467646196549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22926194922982978430797699 34389292384474467646196549)
        ·
          refine ⟨6447992322088962683661853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34389292384474467646196549 6447992322088962683661853)
          ·
            refine ⟨2417997120783361006373195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6447992322088962683661853 2417997120783361006373195)
            ·
              refine ⟨3626995681175041509559793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2417997120783361006373195 3626995681175041509559793)
              ·
                refine ⟨2720246760881281132169845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3626995681175041509559793 2720246760881281132169845)
                ·
                  refine ⟨255023133832620106140923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2720246760881281132169845 255023133832620106140923)
                  ·
                    rfl

theorem cell22_2234951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 5].length) (baseStart_2234951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2234951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2234951 prefixEnd_2234951 := by exact prefixLift 2234951
  have htrace : WordTrace (prefixWord ++ tailWord_2234951) baseStart_2234951 baseEnd_2234951 := by
    simpa [prefixWord, tailWord_2234951, baseEnd_2234951] using wordTrace_append hprefix tailTrace_2234951
  have hstable : (prefixWord ++ tailWord_2234951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2234951).length < 2 ^ (prefixWord ++ tailWord_2234951).sum := by decide
  have hdescent : baseEnd_2234951 < baseStart_2234951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2234951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235013 : List Nat := [1, 3, 1, 1, 4, 3, 3, 2, 4]
def baseStart_2235013 : Nat := 118140960795 + 2235013 * 2 ^ 59
def prefixEnd_2235013 : Nat := 4983230072969 + 3 ^ 40 * 2235013 * 2
def baseEnd_2235013 : Nat := 255030208454970941124193

theorem tailTrace_2235013 : CollatzResearch.WordTrace tailWord_2235013 prefixEnd_2235013 255030208454970941124193 := by
  unfold tailWord_2235013
  simp only [CollatzResearch.WordTrace]
  refine ⟨81517621051937085676037693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54345080701291390450691795 81517621051937085676037693)
  ·
    refine ⟨30569107894476407128514135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81517621051937085676037693 30569107894476407128514135)
    ·
      refine ⟨45853661841714610692771203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30569107894476407128514135 45853661841714610692771203)
      ·
        refine ⟨68780492762571916039156805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45853661841714610692771203 68780492762571916039156805)
        ·
          refine ⟨12896342392982234257341901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68780492762571916039156805 12896342392982234257341901)
          ·
            refine ⟨4836128397368337846503213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12896342392982234257341901 4836128397368337846503213)
            ·
              refine ⟨1813548149013126692438705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4836128397368337846503213 1813548149013126692438705)
              ·
                refine ⟨1360161111759845019329029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1813548149013126692438705 1360161111759845019329029)
                ·
                  refine ⟨255030208454970941124193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1360161111759845019329029 255030208454970941124193)
                  ·
                    rfl

theorem cell22_2235013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_2235013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235013 prefixEnd_2235013 := by exact prefixLift 2235013
  have htrace : WordTrace (prefixWord ++ tailWord_2235013) baseStart_2235013 baseEnd_2235013 := by
    simpa [prefixWord, tailWord_2235013, baseEnd_2235013] using wordTrace_append hprefix tailTrace_2235013
  have hstable : (prefixWord ++ tailWord_2235013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235013).length < 2 ^ (prefixWord ++ tailWord_2235013).sum := by decide
  have hdescent : baseEnd_2235013 < baseStart_2235013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235062 : List Nat := [5, 1, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_2235062 : Nat := 118140960795 + 2235062 * 2 ^ 59
def prefixEnd_2235062 : Nat := 4983230072969 + 3 ^ 40 * 2235062 * 2
def baseEnd_2235062 : Nat := 765107399066293028897429

theorem tailTrace_2235062 : CollatzResearch.WordTrace tailWord_2235062 prefixEnd_2235062 765107399066293028897429 := by
  unfold tailWord_2235062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5094963014297472940285715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54346272152506378029714293 5094963014297472940285715)
  ·
    refine ⟨7642444521446209410428573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5094963014297472940285715 7642444521446209410428573)
    ·
      refine ⟨2865916695542328528910715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7642444521446209410428573 2865916695542328528910715)
      ·
        refine ⟨4298875043313492793366073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2865916695542328528910715 4298875043313492793366073)
        ·
          refine ⟨3224156282485119595024555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4298875043313492793366073 3224156282485119595024555)
          ·
            refine ⟨4836234423727679392536833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3224156282485119595024555 4836234423727679392536833)
            ·
              refine ⟨3627175817795759544402625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4836234423727679392536833 3627175817795759544402625)
              ·
                refine ⟨2720381863346819658301969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3627175817795759544402625 2720381863346819658301969)
                ·
                  refine ⟨2040286397510114743726477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2720381863346819658301969 2040286397510114743726477)
                  ·
                    refine ⟨765107399066293028897429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2040286397510114743726477 765107399066293028897429)
                    ·
                      rfl

theorem cell22_2235062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_2235062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235062 prefixEnd_2235062 := by exact prefixLift 2235062
  have htrace : WordTrace (prefixWord ++ tailWord_2235062) baseStart_2235062 baseEnd_2235062 := by
    simpa [prefixWord, tailWord_2235062, baseEnd_2235062] using wordTrace_append hprefix tailTrace_2235062
  have hstable : (prefixWord ++ tailWord_2235062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235062).length < 2 ^ (prefixWord ++ tailWord_2235062).sum := by decide
  have hdescent : baseEnd_2235062 < baseStart_2235062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235086 : List Nat := [4, 1, 1, 1, 3, 2, 2, 3, 5]
def baseStart_2235086 : Nat := 118140960795 + 2235086 * 2 ^ 59
def prefixEnd_2235086 : Nat := 4983230072969 + 3 ^ 40 * 2235086 * 2
def baseEnd_2235086 : Nat := 255038538252254988765785

theorem tailTrace_2235086 : CollatzResearch.WordTrace tailWord_2235086 prefixEnd_2235086 255038538252254988765785 := by
  unfold tailWord_2235086
  simp only [CollatzResearch.WordTrace]
  refine ⟨10190035447584077392930639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54346855720448412762296741 10190035447584077392930639)
  ·
    refine ⟨15285053171376116089395959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10190035447584077392930639 15285053171376116089395959)
    ·
      refine ⟨22927579757064174134093939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15285053171376116089395959 22927579757064174134093939)
      ·
        refine ⟨34391369635596261201140909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22927579757064174134093939 34391369635596261201140909)
        ·
          refine ⟨12896763613348597950427841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34391369635596261201140909 12896763613348597950427841)
          ·
            refine ⟨9672572710011448462820881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12896763613348597950427841 9672572710011448462820881)
            ·
              refine ⟨7254429532508586347115661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9672572710011448462820881 7254429532508586347115661)
              ·
                refine ⟨2720411074690719880168373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7254429532508586347115661 2720411074690719880168373)
                ·
                  refine ⟨255038538252254988765785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2720411074690719880168373 255038538252254988765785)
                  ·
                    rfl

theorem cell22_2235086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_2235086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235086 prefixEnd_2235086 := by exact prefixLift 2235086
  have htrace : WordTrace (prefixWord ++ tailWord_2235086) baseStart_2235086 baseEnd_2235086 := by
    simpa [prefixWord, tailWord_2235086, baseEnd_2235086] using wordTrace_append hprefix tailTrace_2235086
  have hstable : (prefixWord ++ tailWord_2235086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235086).length < 2 ^ (prefixWord ++ tailWord_2235086).sum := by decide
  have hdescent : baseEnd_2235086 < baseStart_2235086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235114 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 10]
def baseStart_2235114 : Nat := 118140960795 + 2235114 * 2 ^ 59
def prefixEnd_2235114 : Nat := 4983230072969 + 3 ^ 40 * 2235114 * 2
def baseEnd_2235114 : Nat := 255041733242994075532423

theorem tailTrace_2235114 : CollatzResearch.WordTrace tailWord_2235114 prefixEnd_2235114 255041733242994075532423 := by
  unfold tailWord_2235114
  simp only [CollatzResearch.WordTrace]
  refine ⟨20380326206142794981366099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54347536549714119950309597 20380326206142794981366099)
  ·
    refine ⟨30570489309214192472049149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20380326206142794981366099 30570489309214192472049149)
    ·
      refine ⟨11463933490955322177018431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30570489309214192472049149 11463933490955322177018431)
      ·
        refine ⟨17195900236432983265527647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11463933490955322177018431 17195900236432983265527647)
        ·
          refine ⟨25793850354649474898291471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17195900236432983265527647 25793850354649474898291471)
          ·
            refine ⟨38690775531974212347437207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25793850354649474898291471 38690775531974212347437207)
            ·
              refine ⟨58036163297961318521155811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38690775531974212347437207 58036163297961318521155811)
              ·
                refine ⟨87054244946941977781733717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58036163297961318521155811 87054244946941977781733717)
                ·
                  refine ⟨255041733242994075532423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 87054244946941977781733717 255041733242994075532423)
                  ·
                    rfl

theorem cell22_2235114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_2235114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235114 prefixEnd_2235114 := by exact prefixLift 2235114
  have htrace : WordTrace (prefixWord ++ tailWord_2235114) baseStart_2235114 baseEnd_2235114 := by
    simpa [prefixWord, tailWord_2235114, baseEnd_2235114] using wordTrace_append hprefix tailTrace_2235114
  have hstable : (prefixWord ++ tailWord_2235114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235114).length < 2 ^ (prefixWord ++ tailWord_2235114).sum := by decide
  have hdescent : baseEnd_2235114 < baseStart_2235114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235129 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 3, 5]
def baseStart_2235129 : Nat := 118140960795 + 2235129 * 2 ^ 59
def prefixEnd_2235129 : Nat := 4983230072969 + 3 ^ 40 * 2235129 * 2
def baseEnd_2235129 : Nat := 765130334535527187472223

theorem tailTrace_2235129 : CollatzResearch.WordTrace tailWord_2235129 prefixEnd_2235129 765130334535527187472223 := by
  unfold tailWord_2235129
  simp only [CollatzResearch.WordTrace]
  refine ⟨81521851919516837487260441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54347901279677891658173627 81521851919516837487260441)
  ·
    refine ⟨61141388939637628115445331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81521851919516837487260441 61141388939637628115445331)
    ·
      refine ⟨91712083409456442173167997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61141388939637628115445331 91712083409456442173167997)
      ·
        refine ⟨34392031278546165814937999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91712083409456442173167997 34392031278546165814937999)
        ·
          refine ⟨51588046917819248722406999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34392031278546165814937999 51588046917819248722406999)
          ·
            refine ⟨77382070376728873083610499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51588046917819248722406999 77382070376728873083610499)
            ·
              refine ⟨116073105565093309625415749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77382070376728873083610499 116073105565093309625415749)
              ·
                refine ⟨21763707293454995554765453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116073105565093309625415749 21763707293454995554765453)
                ·
                  refine ⟨8161390235045623333037045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21763707293454995554765453 8161390235045623333037045)
                  ·
                    refine ⟨765130334535527187472223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8161390235045623333037045 765130334535527187472223)
                    ·
                      rfl

theorem cell22_2235129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_2235129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235129 prefixEnd_2235129 := by exact prefixLift 2235129
  have htrace : WordTrace (prefixWord ++ tailWord_2235129) baseStart_2235129 baseEnd_2235129 := by
    simpa [prefixWord, tailWord_2235129, baseEnd_2235129] using wordTrace_append hprefix tailTrace_2235129
  have hstable : (prefixWord ++ tailWord_2235129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235129).length < 2 ^ (prefixWord ++ tailWord_2235129).sum := by decide
  have hdescent : baseEnd_2235129 < baseStart_2235129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235182 : List Nat := [4, 1, 3, 2, 1, 2, 3, 2, 4]
def baseStart_2235182 : Nat := 118140960795 + 2235182 * 2 ^ 59
def prefixEnd_2235182 : Nat := 4983230072969 + 3 ^ 40 * 2235182 * 2
def baseEnd_2235182 : Nat := 255049492506217571965687

theorem tailTrace_2235182 : CollatzResearch.WordTrace tailWord_2235182 prefixEnd_2235182 255049492506217571965687 := by
  unfold tailWord_2235182
  simp only [CollatzResearch.WordTrace]
  refine ⟨10190473123540603442367475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54349189992216551692626533 10190473123540603442367475)
  ·
    refine ⟨15285709685310905163551213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10190473123540603442367475 15285709685310905163551213)
    ·
      refine ⟨5732141131991589436331705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15285709685310905163551213 5732141131991589436331705)
      ·
        refine ⟨4299105848993692077248779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5732141131991589436331705 4299105848993692077248779)
        ·
          refine ⟨6448658773490538115873169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4299105848993692077248779 6448658773490538115873169)
          ·
            refine ⟨4836494080117903586904877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6448658773490538115873169 4836494080117903586904877)
            ·
              refine ⟨1813685280044213845089329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4836494080117903586904877 1813685280044213845089329)
              ·
                refine ⟨1360263960033160383816997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1813685280044213845089329 1360263960033160383816997)
                ·
                  refine ⟨255049492506217571965687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1360263960033160383816997 255049492506217571965687)
                  ·
                    rfl

theorem cell22_2235182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_2235182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235182 prefixEnd_2235182 := by exact prefixLift 2235182
  have htrace : WordTrace (prefixWord ++ tailWord_2235182) baseStart_2235182 baseEnd_2235182 := by
    simpa [prefixWord, tailWord_2235182, baseEnd_2235182] using wordTrace_append hprefix tailTrace_2235182
  have hstable : (prefixWord ++ tailWord_2235182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235182).length < 2 ^ (prefixWord ++ tailWord_2235182).sum := by decide
  have hdescent : baseEnd_2235182 < baseStart_2235182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235251 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 3, 4]
def baseStart_2235251 : Nat := 118140960795 + 2235251 * 2 ^ 59
def prefixEnd_2235251 : Nat := 4983230072969 + 3 ^ 40 * 2235251 * 2
def baseEnd_2235251 : Nat := 765172097628759535921849

theorem tailTrace_2235251 : CollatzResearch.WordTrace tailWord_2235251 prefixEnd_2235251 765172097628759535921849 := by
  unfold tailWord_2235251
  simp only [CollatzResearch.WordTrace]
  refine ⟨81526301625074852323201607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54350867750049901548801071 81526301625074852323201607)
  ·
    refine ⟨122289452437612278484802411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81526301625074852323201607 122289452437612278484802411)
    ·
      refine ⟨183434178656418417727203617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122289452437612278484802411 183434178656418417727203617)
      ·
        refine ⟨137575633992313813295402713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183434178656418417727203617 137575633992313813295402713)
        ·
          refine ⟨103181725494235359971552035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137575633992313813295402713 103181725494235359971552035)
          ·
            refine ⟨154772588241353039957328053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103181725494235359971552035 154772588241353039957328053)
            ·
              refine ⟨14509930147626847495999505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 154772588241353039957328053 14509930147626847495999505)
              ·
                refine ⟨10882447610720135621999629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14509930147626847495999505 10882447610720135621999629)
                ·
                  refine ⟨4080917854020050858249861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10882447610720135621999629 4080917854020050858249861)
                  ·
                    refine ⟨765172097628759535921849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4080917854020050858249861 765172097628759535921849)
                    ·
                      rfl

theorem cell22_2235251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 4].length) (baseStart_2235251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235251 prefixEnd_2235251 := by exact prefixLift 2235251
  have htrace : WordTrace (prefixWord ++ tailWord_2235251) baseStart_2235251 baseEnd_2235251 := by
    simpa [prefixWord, tailWord_2235251, baseEnd_2235251] using wordTrace_append hprefix tailTrace_2235251
  have hstable : (prefixWord ++ tailWord_2235251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235251).length < 2 ^ (prefixWord ++ tailWord_2235251).sum := by decide
  have hdescent : baseEnd_2235251 < baseStart_2235251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235253 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 2, 5]
def baseStart_2235253 : Nat := 118140960795 + 2235253 * 2 ^ 59
def prefixEnd_2235253 : Nat := 4983230072969 + 3 ^ 40 * 2235253 * 2
def baseEnd_2235253 : Nat := 765172782269632197371843

theorem tailTrace_2235253 : CollatzResearch.WordTrace tailWord_2235253 prefixEnd_2235253 765172782269632197371843 := by
  unfold tailWord_2235253
  simp only [CollatzResearch.WordTrace]
  refine ⟨81526374571067606664774413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54350916380711737776516275 81526374571067606664774413)
  ·
    refine ⟨30572390464150352499290405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81526374571067606664774413 30572390464150352499290405)
    ·
      refine ⟨5732323212028191093616951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30572390464150352499290405 5732323212028191093616951)
      ·
        refine ⟨8598484818042286640425427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5732323212028191093616951 8598484818042286640425427)
        ·
          refine ⟨12897727227063429960638141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8598484818042286640425427 12897727227063429960638141)
          ·
            refine ⟨4836647710148786235239303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12897727227063429960638141 4836647710148786235239303)
            ·
              refine ⟨7254971565223179352858955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4836647710148786235239303 7254971565223179352858955)
              ·
                refine ⟨10882457347834769029288433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7254971565223179352858955 10882457347834769029288433)
                ·
                  refine ⟨8161843010876076771966325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10882457347834769029288433 8161843010876076771966325)
                  ·
                    refine ⟨765172782269632197371843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8161843010876076771966325 765172782269632197371843)
                    ·
                      rfl

theorem cell22_2235253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_2235253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235253 prefixEnd_2235253 := by exact prefixLift 2235253
  have htrace : WordTrace (prefixWord ++ tailWord_2235253) baseStart_2235253 baseEnd_2235253 := by
    simpa [prefixWord, tailWord_2235253, baseEnd_2235253] using wordTrace_append hprefix tailTrace_2235253
  have hstable : (prefixWord ++ tailWord_2235253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235253).length < 2 ^ (prefixWord ++ tailWord_2235253).sum := by decide
  have hdescent : baseEnd_2235253 < baseStart_2235253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235268 : List Nat := [2, 3, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_2235268 : Nat := 118140960795 + 2235268 * 2 ^ 59
def prefixEnd_2235268 : Nat := 4983230072969 + 3 ^ 40 * 2235268 * 2
def baseEnd_2235268 : Nat := 765177917076177158246797

theorem tailTrace_2235268 : CollatzResearch.WordTrace tailWord_2235268 prefixEnd_2235268 765177917076177158246797 := by
  unfold tailWord_2235268
  simp only [CollatzResearch.WordTrace]
  refine ⟨40763460833006632113285229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54351281110675509484380305 40763460833006632113285229)
  ·
    refine ⟨15286297812377487042481961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40763460833006632113285229 15286297812377487042481961)
    ·
      refine ⟨11464723359283115281861471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15286297812377487042481961 11464723359283115281861471)
      ·
        refine ⟨17197085038924672922792207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11464723359283115281861471 17197085038924672922792207)
        ·
          refine ⟨25795627558387009384188311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17197085038924672922792207 25795627558387009384188311)
          ·
            refine ⟨38693441337580514076282467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25795627558387009384188311 38693441337580514076282467)
            ·
              refine ⟨58040162006370771114423701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38693441337580514076282467 58040162006370771114423701)
              ·
                refine ⟨2720632594048629895988611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58040162006370771114423701 2720632594048629895988611)
                ·
                  refine ⟨4080948891072944843982917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2720632594048629895988611 4080948891072944843982917)
                  ·
                    refine ⟨765177917076177158246797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4080948891072944843982917 765177917076177158246797)
                    ·
                      rfl

theorem cell22_2235268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_2235268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235268 prefixEnd_2235268 := by exact prefixLift 2235268
  have htrace : WordTrace (prefixWord ++ tailWord_2235268) baseStart_2235268 baseEnd_2235268 := by
    simpa [prefixWord, tailWord_2235268, baseEnd_2235268] using wordTrace_append hprefix tailTrace_2235268
  have hstable : (prefixWord ++ tailWord_2235268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235268).length < 2 ^ (prefixWord ++ tailWord_2235268).sum := by decide
  have hdescent : baseEnd_2235268 < baseStart_2235268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235285 : List Nat := [1, 3, 2, 1, 1, 4, 4, 1, 1, 4]
def baseStart_2235285 : Nat := 118140960795 + 2235285 * 2 ^ 59
def prefixEnd_2235285 : Nat := 4983230072969 + 3 ^ 40 * 2235285 * 2
def baseEnd_2235285 : Nat := 765183736523594780571745

theorem tailTrace_2235285 : CollatzResearch.WordTrace tailWord_2235285 prefixEnd_2235285 765183736523594780571745 := by
  unfold tailWord_2235285
  simp only [CollatzResearch.WordTrace]
  refine ⟨81527541706951676129939309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54351694471301117419959539 81527541706951676129939309)
  ·
    refine ⟨30572828140106878548727241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81527541706951676129939309 30572828140106878548727241)
    ·
      refine ⟨22929621105080158911545431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30572828140106878548727241 22929621105080158911545431)
      ·
        refine ⟨34394431657620238367318147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22929621105080158911545431 34394431657620238367318147)
        ·
          refine ⟨51591647486430357550977221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34394431657620238367318147 51591647486430357550977221)
          ·
            refine ⟨9673433903705692040808229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51591647486430357550977221 9673433903705692040808229)
            ·
              refine ⟨1813768856944817257651543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9673433903705692040808229 1813768856944817257651543)
              ·
                refine ⟨2720653285417225886477315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1813768856944817257651543 2720653285417225886477315)
                ·
                  refine ⟨4080979928125838829715973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2720653285417225886477315 4080979928125838829715973)
                  ·
                    refine ⟨765183736523594780571745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4080979928125838829715973 765183736523594780571745)
                    ·
                      rfl

theorem cell22_2235285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_2235285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235285 prefixEnd_2235285 := by exact prefixLift 2235285
  have htrace : WordTrace (prefixWord ++ tailWord_2235285) baseStart_2235285 baseEnd_2235285 := by
    simpa [prefixWord, tailWord_2235285, baseEnd_2235285] using wordTrace_append hprefix tailTrace_2235285
  have hstable : (prefixWord ++ tailWord_2235285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235285).length < 2 ^ (prefixWord ++ tailWord_2235285).sum := by decide
  have hdescent : baseEnd_2235285 < baseStart_2235285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235328 : List Nat := [2, 1, 1, 2, 3, 3, 4, 6]
def baseStart_2235328 : Nat := 118140960795 + 2235328 * 2 ^ 59
def prefixEnd_2235328 : Nat := 4983230072969 + 3 ^ 40 * 2235328 * 2
def baseEnd_2235328 : Nat := 85022050700261889082957

theorem tailTrace_2235328 : CollatzResearch.WordTrace tailWord_2235328 prefixEnd_2235328 85022050700261889082957 := by
  unfold tailWord_2235328
  simp only [CollatzResearch.WordTrace]
  refine ⟨40764555022897947236877319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54352740030530596315836425 40764555022897947236877319)
  ·
    refine ⟨61146832534346920855315979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40764555022897947236877319 61146832534346920855315979)
    ·
      refine ⟨91720248801520381282973969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61146832534346920855315979 91720248801520381282973969)
      ·
        refine ⟨68790186601140285962230477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91720248801520381282973969 68790186601140285962230477)
        ·
          refine ⟨25796319975427607235836429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68790186601140285962230477 25796319975427607235836429)
          ·
            refine ⟨9673619990785352713438661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25796319975427607235836429 9673619990785352713438661)
            ·
              refine ⟨1813803748272253633769749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9673619990785352713438661 1813803748272253633769749)
              ·
                refine ⟨85022050700261889082957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1813803748272253633769749 85022050700261889082957)
                ·
                  rfl

theorem cell22_2235328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 6].length) (baseStart_2235328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235328 prefixEnd_2235328 := by exact prefixLift 2235328
  have htrace : WordTrace (prefixWord ++ tailWord_2235328) baseStart_2235328 baseEnd_2235328 := by
    simpa [prefixWord, tailWord_2235328, baseEnd_2235328] using wordTrace_append hprefix tailTrace_2235328
  have hstable : (prefixWord ++ tailWord_2235328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235328).length < 2 ^ (prefixWord ++ tailWord_2235328).sum := by decide
  have hdescent : baseEnd_2235328 < baseStart_2235328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235418 : List Nat := [3, 1, 1, 3, 1, 2, 2, 3, 6]
def baseStart_2235418 : Nat := 118140960795 + 2235418 * 2 ^ 59
def prefixEnd_2235418 : Nat := 4983230072969 + 3 ^ 40 * 2235418 * 2
def baseEnd_2235418 : Nat := 255076421713875588998779

theorem tailTrace_2235418 : CollatzResearch.WordTrace tailWord_2235418 prefixEnd_2235418 255076421713875588998779 := by
  unfold tailWord_2235418
  simp only [CollatzResearch.WordTrace]
  refine ⟨20383098153867459961132727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54354928410313226563020605 20383098153867459961132727)
  ·
    refine ⟨30574647230801189941699091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20383098153867459961132727 30574647230801189941699091)
    ·
      refine ⟨45861970846201784912548637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30574647230801189941699091 45861970846201784912548637)
      ·
        refine ⟨17198239067325669342205739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45861970846201784912548637 17198239067325669342205739)
        ·
          refine ⟨25797358600988504013308609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17198239067325669342205739 25797358600988504013308609)
          ·
            refine ⟨19348018950741378009981457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25797358600988504013308609 19348018950741378009981457)
            ·
              refine ⟨14511014213056033507486093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19348018950741378009981457 14511014213056033507486093)
              ·
                refine ⟨5441630329896012565307285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14511014213056033507486093 5441630329896012565307285)
                ·
                  refine ⟨255076421713875588998779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5441630329896012565307285 255076421713875588998779)
                  ·
                    rfl

theorem cell22_2235418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_2235418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235418 prefixEnd_2235418 := by exact prefixLift 2235418
  have htrace : WordTrace (prefixWord ++ tailWord_2235418) baseStart_2235418 baseEnd_2235418 := by
    simpa [prefixWord, tailWord_2235418, baseEnd_2235418] using wordTrace_append hprefix tailTrace_2235418
  have hstable : (prefixWord ++ tailWord_2235418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235418).length < 2 ^ (prefixWord ++ tailWord_2235418).sum := by decide
  have hdescent : baseEnd_2235418 < baseStart_2235418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235452 : List Nat := [2, 2, 2, 2, 2, 3, 2, 3, 4]
def baseStart_2235452 : Nat := 118140960795 + 2235452 * 2 ^ 59
def prefixEnd_2235452 : Nat := 4983230072969 + 3 ^ 40 * 2235452 * 2
def baseEnd_2235452 : Nat := 255080301345487337215411

theorem tailTrace_2235452 : CollatzResearch.WordTrace tailWord_2235452 prefixEnd_2235452 255080301345487337215411 := by
  unfold tailWord_2235452
  simp only [CollatzResearch.WordTrace]
  refine ⟨40766816348673331825634305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54355755131564442434179073 40766816348673331825634305)
  ·
    refine ⟨30575112261504998869225729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40766816348673331825634305 30575112261504998869225729)
    ·
      refine ⟨22931334196128749151919297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30575112261504998869225729 22931334196128749151919297)
      ·
        refine ⟨17198500647096561863939473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22931334196128749151919297 17198500647096561863939473)
        ·
          refine ⟨12898875485322421397954605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17198500647096561863939473 12898875485322421397954605)
          ·
            refine ⟨4837078306995908024232977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12898875485322421397954605 4837078306995908024232977)
            ·
              refine ⟨3627808730246931018174733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4837078306995908024232977 3627808730246931018174733)
              ·
                refine ⟨1360428273842599131815525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3627808730246931018174733 1360428273842599131815525)
                ·
                  refine ⟨255080301345487337215411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1360428273842599131815525 255080301345487337215411)
                  ·
                    rfl

theorem cell22_2235452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_2235452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235452 prefixEnd_2235452 := by exact prefixLift 2235452
  have htrace : WordTrace (prefixWord ++ tailWord_2235452) baseStart_2235452 baseEnd_2235452 := by
    simpa [prefixWord, tailWord_2235452, baseEnd_2235452] using wordTrace_append hprefix tailTrace_2235452
  have hstable : (prefixWord ++ tailWord_2235452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235452).length < 2 ^ (prefixWord ++ tailWord_2235452).sum := by decide
  have hdescent : baseEnd_2235452 < baseStart_2235452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235454 : List Nat := [4, 2, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_2235454 : Nat := 118140960795 + 2235454 * 2 ^ 59
def prefixEnd_2235454 : Nat := 4983230072969 + 3 ^ 40 * 2235454 * 2
def baseEnd_2235454 : Nat := 765241588677334673096227

theorem tailTrace_2235454 : CollatzResearch.WordTrace tailWord_2235454 prefixEnd_2235454 765241588677334673096227 := by
  unfold tailWord_2235454
  simp only [CollatzResearch.WordTrace]
  refine ⟨10191713205417427249105177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54355803762226278661894277 10191713205417427249105177)
  ·
    refine ⟨7643784904063070436828883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10191713205417427249105177 7643784904063070436828883)
    ·
      refine ⟨11465677356094605655243325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7643784904063070436828883 11465677356094605655243325)
      ·
        refine ⟨4299629008535477120716247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11465677356094605655243325 4299629008535477120716247)
        ·
          refine ⟨6449443512803215681074371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4299629008535477120716247 6449443512803215681074371)
          ·
            refine ⟨9674165269204823521611557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6449443512803215681074371 9674165269204823521611557)
            ·
              refine ⟨1813905987975904410302167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9674165269204823521611557 1813905987975904410302167)
              ·
                refine ⟨2720858981963856615453251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1813905987975904410302167 2720858981963856615453251)
                ·
                  refine ⟨4081288472945784923179877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2720858981963856615453251 4081288472945784923179877)
                  ·
                    refine ⟨765241588677334673096227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4081288472945784923179877 765241588677334673096227)
                    ·
                      rfl

theorem cell22_2235454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_2235454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235454 prefixEnd_2235454 := by exact prefixLift 2235454
  have htrace : WordTrace (prefixWord ++ tailWord_2235454) baseStart_2235454 baseEnd_2235454 := by
    simpa [prefixWord, tailWord_2235454, baseEnd_2235454] using wordTrace_append hprefix tailTrace_2235454
  have hstable : (prefixWord ++ tailWord_2235454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235454).length < 2 ^ (prefixWord ++ tailWord_2235454).sum := by decide
  have hdescent : baseEnd_2235454 < baseStart_2235454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235463 : List Nat := [1, 1, 4, 1, 3, 3, 9]
def baseStart_2235463 : Nat := 118140960795 + 2235463 * 2 ^ 59
def prefixEnd_2235463 : Nat := 4983230072969 + 3 ^ 40 * 2235463 * 2
def baseEnd_2235463 : Nat := 28342395168935616652637

theorem tailTrace_2235463 : CollatzResearch.WordTrace tailWord_2235463 prefixEnd_2235463 28342395168935616652637 := by
  unfold tailWord_2235463
  simp only [CollatzResearch.WordTrace]
  refine ⟨81534033900306812529919043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54356022600204541686612695 81534033900306812529919043)
  ·
    refine ⟨122301050850460218794878565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81534033900306812529919043 122301050850460218794878565)
    ·
      refine ⟨22931447034461291024039731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122301050850460218794878565 22931447034461291024039731)
      ·
        refine ⟨34397170551691936536059597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22931447034461291024039731 34397170551691936536059597)
        ·
          refine ⟨12898938956884476201022349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34397170551691936536059597 12898938956884476201022349)
          ·
            refine ⟨4837102108831678575383381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12898938956884476201022349 4837102108831678575383381)
            ·
              refine ⟨28342395168935616652637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4837102108831678575383381 28342395168935616652637)
              ·
                rfl

theorem cell22_2235463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 9].length) (baseStart_2235463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235463 prefixEnd_2235463 := by exact prefixLift 2235463
  have htrace : WordTrace (prefixWord ++ tailWord_2235463) baseStart_2235463 baseEnd_2235463 := by
    simpa [prefixWord, tailWord_2235463, baseEnd_2235463] using wordTrace_append hprefix tailTrace_2235463
  have hstable : (prefixWord ++ tailWord_2235463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235463).length < 2 ^ (prefixWord ++ tailWord_2235463).sum := by decide
  have hdescent : baseEnd_2235463 < baseStart_2235463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235484 : List Nat := [2, 2, 4, 1, 1, 1, 5, 1, 2, 3]
def baseStart_2235484 : Nat := 118140960795 + 2235484 * 2 ^ 59
def prefixEnd_2235484 : Nat := 4983230072969 + 3 ^ 40 * 2235484 * 2
def baseEnd_2235484 : Nat := 765251858290424594846135

theorem tailTrace_2235484 : CollatzResearch.WordTrace tailWord_2235484 prefixEnd_2235484 765251858290424594846135 := by
  unfold tailWord_2235484
  simp only [CollatzResearch.WordTrace]
  refine ⟨40767399916615366558216753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54356533222153822077622337 40767399916615366558216753)
  ·
    refine ⟨30575549937461524918662565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40767399916615366558216753 30575549937461524918662565)
    ·
      refine ⟨5732915613274035922249231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30575549937461524918662565 5732915613274035922249231)
      ·
        refine ⟨8599373419911053883373847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5732915613274035922249231 8599373419911053883373847)
        ·
          refine ⟨12899060129866580825060771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8599373419911053883373847 12899060129866580825060771)
          ·
            refine ⟨19348590194799871237591157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12899060129866580825060771 19348590194799871237591157)
            ·
              refine ⟨1813930330762487928524171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19348590194799871237591157 1813930330762487928524171)
              ·
                refine ⟨2720895496143731892786257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1813930330762487928524171 2720895496143731892786257)
                ·
                  refine ⟨2040671622107798919589693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2720895496143731892786257 2040671622107798919589693)
                  ·
                    refine ⟨765251858290424594846135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2040671622107798919589693 765251858290424594846135)
                    ·
                      rfl

theorem cell22_2235484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_2235484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235484 prefixEnd_2235484 := by exact prefixLift 2235484
  have htrace : WordTrace (prefixWord ++ tailWord_2235484) baseStart_2235484 baseEnd_2235484 := by
    simpa [prefixWord, tailWord_2235484, baseEnd_2235484] using wordTrace_append hprefix tailTrace_2235484
  have hstable : (prefixWord ++ tailWord_2235484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235484).length < 2 ^ (prefixWord ++ tailWord_2235484).sum := by decide
  have hdescent : baseEnd_2235484 < baseStart_2235484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235602 : List Nat := [3, 2, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_2235602 : Nat := 118140960795 + 2235602 * 2 ^ 59
def prefixEnd_2235602 : Nat := 4983230072969 + 3 ^ 40 * 2235602 * 2
def baseEnd_2235602 : Nat := 765292252101911620395773

theorem tailTrace_2235602 : CollatzResearch.WordTrace tailWord_2235602 prefixEnd_2235602 765292252101911620395773 := by
  unfold tailWord_2235602
  simp only [CollatzResearch.WordTrace]
  refine ⟨20384775911700809817307265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54359402431202159512819373 20384775911700809817307265)
  ·
    refine ⟨15288581933775607362980449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20384775911700809817307265 15288581933775607362980449)
    ·
      refine ⟨11466436450331705522235337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15288581933775607362980449 11466436450331705522235337)
      ·
        refine ⟨8599827337748779141676503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11466436450331705522235337 8599827337748779141676503)
        ·
          refine ⟨12899741006623168712514755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8599827337748779141676503 12899741006623168712514755)
          ·
            refine ⟨19349611509934753068772133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12899741006623168712514755 19349611509934753068772133)
            ·
              refine ⟨3628052158112766200394775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19349611509934753068772133 3628052158112766200394775)
              ·
                refine ⟨5442078237169149300592163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3628052158112766200394775 5442078237169149300592163)
                ·
                  refine ⟨8163117355753723950888245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5442078237169149300592163 8163117355753723950888245)
                  ·
                    refine ⟨765292252101911620395773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8163117355753723950888245 765292252101911620395773)
                    ·
                      rfl

theorem cell22_2235602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_2235602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235602 prefixEnd_2235602 := by exact prefixLift 2235602
  have htrace : WordTrace (prefixWord ++ tailWord_2235602) baseStart_2235602 baseEnd_2235602 := by
    simpa [prefixWord, tailWord_2235602, baseEnd_2235602] using wordTrace_append hprefix tailTrace_2235602
  have hstable : (prefixWord ++ tailWord_2235602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235602).length < 2 ^ (prefixWord ++ tailWord_2235602).sum := by decide
  have hdescent : baseEnd_2235602 < baseStart_2235602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235604 : List Nat := [2, 4, 1, 4, 1, 1, 1, 2, 6]
def baseStart_2235604 : Nat := 118140960795 + 2235604 * 2 ^ 59
def prefixEnd_2235604 : Nat := 4983230072969 + 3 ^ 40 * 2235604 * 2
def baseEnd_2235604 : Nat := 255097645580928093948589

theorem tailTrace_2235604 : CollatzResearch.WordTrace tailWord_2235604 prefixEnd_2235604 255097645580928093948589 := by
  unfold tailWord_2235604
  simp only [CollatzResearch.WordTrace]
  refine ⟨40769588296397996805400933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54359451061863995740534577 40769588296397996805400933)
  ·
    refine ⟨7644297805574624401012675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40769588296397996805400933 7644297805574624401012675)
    ·
      refine ⟨11466446708361936601519013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7644297805574624401012675 11466446708361936601519013)
      ·
        refine ⟨2149958757817863112784815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11466446708361936601519013 2149958757817863112784815)
        ·
          refine ⟨3224938136726794669177223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2149958757817863112784815 3224938136726794669177223)
          ·
            refine ⟨4837407205090192003765835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3224938136726794669177223 4837407205090192003765835)
            ·
              refine ⟨7256110807635288005648753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4837407205090192003765835 7256110807635288005648753)
              ·
                refine ⟨5442083105726466004236565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7256110807635288005648753 5442083105726466004236565)
                ·
                  refine ⟨255097645580928093948589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5442083105726466004236565 255097645580928093948589)
                  ·
                    rfl

theorem cell22_2235604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_2235604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235604 prefixEnd_2235604 := by exact prefixLift 2235604
  have htrace : WordTrace (prefixWord ++ tailWord_2235604) baseStart_2235604 baseEnd_2235604 := by
    simpa [prefixWord, tailWord_2235604, baseEnd_2235604] using wordTrace_append hprefix tailTrace_2235604
  have hstable : (prefixWord ++ tailWord_2235604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235604).length < 2 ^ (prefixWord ++ tailWord_2235604).sum := by decide
  have hdescent : baseEnd_2235604 < baseStart_2235604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235617 : List Nat := [1, 2, 3, 1, 3, 2, 3, 1, 2, 4]
def baseStart_2235617 : Nat := 118140960795 + 2235617 * 2 ^ 59
def prefixEnd_2235617 : Nat := 4983230072969 + 3 ^ 40 * 2235617 * 2
def baseEnd_2235617 : Nat := 765297386908456581270727

theorem tailTrace_2235617 : CollatzResearch.WordTrace tailWord_2235617 prefixEnd_2235617 765297386908456581270727 := by
  unfold tailWord_2235617
  simp only [CollatzResearch.WordTrace]
  refine ⟨81539650741748896831025105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54359767161165931220683403 81539650741748896831025105)
  ·
    refine ⟨61154738056311672623268829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81539650741748896831025105 61154738056311672623268829)
    ·
      refine ⟨22933026771116877233725811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61154738056311672623268829 22933026771116877233725811)
      ·
        refine ⟨34399540156675315850588717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22933026771116877233725811 34399540156675315850588717)
        ·
          refine ⟨12899827558753243443970769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34399540156675315850588717 12899827558753243443970769)
          ·
            refine ⟨9674870669064932582978077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12899827558753243443970769 9674870669064932582978077)
            ·
              refine ⟨3628076500899349718616779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9674870669064932582978077 3628076500899349718616779)
              ·
                refine ⟨5442114751349024577925169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3628076500899349718616779 5442114751349024577925169)
                ·
                  refine ⟨4081586063511768433443877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5442114751349024577925169 4081586063511768433443877)
                  ·
                    refine ⟨765297386908456581270727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4081586063511768433443877 765297386908456581270727)
                    ·
                      rfl

theorem cell22_2235617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_2235617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235617 prefixEnd_2235617 := by exact prefixLift 2235617
  have htrace : WordTrace (prefixWord ++ tailWord_2235617) baseStart_2235617 baseEnd_2235617 := by
    simpa [prefixWord, tailWord_2235617, baseEnd_2235617] using wordTrace_append hprefix tailTrace_2235617
  have hstable : (prefixWord ++ tailWord_2235617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235617).length < 2 ^ (prefixWord ++ tailWord_2235617).sum := by decide
  have hdescent : baseEnd_2235617 < baseStart_2235617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235623 : List Nat := [1, 1, 5, 3, 3, 1, 2, 1, 1, 4]
def baseStart_2235623 : Nat := 118140960795 + 2235623 * 2 ^ 59
def prefixEnd_2235623 : Nat := 4983230072969 + 3 ^ 40 * 2235623 * 2
def baseEnd_2235623 : Nat := 765299440831074565620709

theorem tailTrace_2235623 : CollatzResearch.WordTrace tailWord_2235623 prefixEnd_2235623 765299440831074565620709 := by
  unfold tailWord_2235623
  simp only [CollatzResearch.WordTrace]
  refine ⟨81539869579727159855743523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54359913053151439903829015 81539869579727159855743523)
  ·
    refine ⟨122309804369590739783615285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81539869579727159855743523 122309804369590739783615285)
    ·
      refine ⟨11466544159649131854713933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122309804369590739783615285 11466544159649131854713933)
      ·
        refine ⟨4299954059868424445517725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11466544159649131854713933 4299954059868424445517725)
        ·
          refine ⟨1612482772450659167069147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4299954059868424445517725 1612482772450659167069147)
          ·
            refine ⟨2418724158675988750603721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1612482772450659167069147 2418724158675988750603721)
            ·
              refine ⟨1814043119006991562952791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2418724158675988750603721 1814043119006991562952791)
              ·
                refine ⟨2721064678510487344429187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1814043119006991562952791 2721064678510487344429187)
                ·
                  refine ⟨4081597017765731016643781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2721064678510487344429187 4081597017765731016643781)
                  ·
                    refine ⟨765299440831074565620709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4081597017765731016643781 765299440831074565620709)
                    ·
                      rfl

theorem cell22_2235623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_2235623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235623 prefixEnd_2235623 := by exact prefixLift 2235623
  have htrace : WordTrace (prefixWord ++ tailWord_2235623) baseStart_2235623 baseEnd_2235623 := by
    simpa [prefixWord, tailWord_2235623, baseEnd_2235623] using wordTrace_append hprefix tailTrace_2235623
  have hstable : (prefixWord ++ tailWord_2235623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235623).length < 2 ^ (prefixWord ++ tailWord_2235623).sum := by decide
  have hdescent : baseEnd_2235623 < baseStart_2235623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235647 : List Nat := [1, 1, 2, 2, 1, 5, 1, 3, 3, 3]
def baseStart_2235647 : Nat := 118140960795 + 2235647 * 2 ^ 59
def prefixEnd_2235647 : Nat := 4983230072969 + 3 ^ 40 * 2235647 * 2
def baseEnd_2235647 : Nat := 765307656521546503020635

theorem tailTrace_2235647 : CollatzResearch.WordTrace tailWord_2235647 prefixEnd_2235647 765307656521546503020635 := by
  unfold tailWord_2235647
  simp only [CollatzResearch.WordTrace]
  refine ⟨81540744931640211954617195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54360496621093474636411463 81540744931640211954617195)
  ·
    refine ⟨122311117397460317931925793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81540744931640211954617195 122311117397460317931925793)
    ·
      refine ⟨91733338048095238448944345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122311117397460317931925793 91733338048095238448944345)
      ·
        refine ⟨68800003536071428836708259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91733338048095238448944345 68800003536071428836708259)
        ·
          refine ⟨103200005304107143255062389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68800003536071428836708259 103200005304107143255062389)
          ·
            refine ⟨9675000497260044680162099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103200005304107143255062389 9675000497260044680162099)
            ·
              refine ⟨14512500745890067020243149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9675000497260044680162099 14512500745890067020243149)
              ·
                refine ⟨5442187779708775132591181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14512500745890067020243149 5442187779708775132591181)
                ·
                  refine ⟨2040820417390790674721693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5442187779708775132591181 2040820417390790674721693)
                  ·
                    refine ⟨765307656521546503020635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2040820417390790674721693 765307656521546503020635)
                    ·
                      rfl

theorem cell22_2235647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 3].length) (baseStart_2235647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235647 prefixEnd_2235647 := by exact prefixLift 2235647
  have htrace : WordTrace (prefixWord ++ tailWord_2235647) baseStart_2235647 baseEnd_2235647 := by
    simpa [prefixWord, tailWord_2235647, baseEnd_2235647] using wordTrace_append hprefix tailTrace_2235647
  have hstable : (prefixWord ++ tailWord_2235647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235647).length < 2 ^ (prefixWord ++ tailWord_2235647).sum := by decide
  have hdescent : baseEnd_2235647 < baseStart_2235647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235677 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 7]
def baseStart_2235677 : Nat := 118140960795 + 2235677 * 2 ^ 59
def prefixEnd_2235677 : Nat := 4983230072969 + 3 ^ 40 * 2235677 * 2
def baseEnd_2235677 : Nat := 255105975378212141590181

theorem tailTrace_2235677 : CollatzResearch.WordTrace tailWord_2235677 prefixEnd_2235677 255105975378212141590181 := by
  unfold tailWord_2235677
  simp only [CollatzResearch.WordTrace]
  refine ⟨81541839121531527078209285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54361226081021018052139523 81541839121531527078209285)
  ·
    refine ⟨15289094835287161327164241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81541839121531527078209285 15289094835287161327164241)
    ·
      refine ⟨11466821126465370995373181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15289094835287161327164241 11466821126465370995373181)
      ·
        refine ⟨4300057922424514123264943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11466821126465370995373181 4300057922424514123264943)
        ·
          refine ⟨6450086883636771184897415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4300057922424514123264943 6450086883636771184897415)
          ·
            refine ⟨9675130325455156777346123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6450086883636771184897415 9675130325455156777346123)
            ·
              refine ⟨14512695488182735166019185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9675130325455156777346123 14512695488182735166019185)
              ·
                refine ⟨10884521616137051374514389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14512695488182735166019185 10884521616137051374514389)
                ·
                  refine ⟨255105975378212141590181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10884521616137051374514389 255105975378212141590181)
                  ·
                    rfl

theorem cell22_2235677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_2235677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235677 prefixEnd_2235677 := by exact prefixLift 2235677
  have htrace : WordTrace (prefixWord ++ tailWord_2235677) baseStart_2235677 baseEnd_2235677 := by
    simpa [prefixWord, tailWord_2235677, baseEnd_2235677] using wordTrace_append hprefix tailTrace_2235677
  have hstable : (prefixWord ++ tailWord_2235677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235677).length < 2 ^ (prefixWord ++ tailWord_2235677).sum := by decide
  have hdescent : baseEnd_2235677 < baseStart_2235677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235698 : List Nat := [3, 2, 1, 1, 4, 2, 3, 2, 1, 3]
def baseStart_2235698 : Nat := 118140960795 + 2235698 * 2 ^ 59
def prefixEnd_2235698 : Nat := 4983230072969 + 3 ^ 40 * 2235698 * 2
def baseEnd_2235698 : Nat := 765325114863799369995479

theorem tailTrace_2235698 : CollatzResearch.WordTrace tailWord_2235698 prefixEnd_2235698 765325114863799369995479 := by
  unfold tailWord_2235698
  simp only [CollatzResearch.WordTrace]
  refine ⟨20385651263613861916180937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54361736702970298443149165 20385651263613861916180937)
  ·
    refine ⟨15289238447710396437135703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20385651263613861916180937 15289238447710396437135703)
    ·
      refine ⟨22933857671565594655703555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15289238447710396437135703 22933857671565594655703555)
      ·
        refine ⟨34400786507348391983555333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22933857671565594655703555 34400786507348391983555333)
        ·
          refine ⟨6450147470127823496916625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34400786507348391983555333 6450147470127823496916625)
          ·
            refine ⟨4837610602595867622687469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6450147470127823496916625 4837610602595867622687469)
            ·
              refine ⟨1814103975973450358507801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4837610602595867622687469 1814103975973450358507801)
              ·
                refine ⟨1360577981980087768880851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1814103975973450358507801 1360577981980087768880851)
                ·
                  refine ⟨2040866972970131653321277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360577981980087768880851 2040866972970131653321277)
                  ·
                    refine ⟨765325114863799369995479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2040866972970131653321277 765325114863799369995479)
                    ·
                      rfl

theorem cell22_2235698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_2235698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235698 prefixEnd_2235698 := by exact prefixLift 2235698
  have htrace : WordTrace (prefixWord ++ tailWord_2235698) baseStart_2235698 baseEnd_2235698 := by
    simpa [prefixWord, tailWord_2235698, baseEnd_2235698] using wordTrace_append hprefix tailTrace_2235698
  have hstable : (prefixWord ++ tailWord_2235698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235698).length < 2 ^ (prefixWord ++ tailWord_2235698).sum := by decide
  have hdescent : baseEnd_2235698 < baseStart_2235698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235724 : List Nat := [2, 2, 1, 3, 2, 2, 3, 2, 1, 4]
def baseStart_2235724 : Nat := 118140960795 + 2235724 * 2 ^ 59
def prefixEnd_2235724 : Nat := 4983230072969 + 3 ^ 40 * 2235724 * 2
def baseEnd_2235724 : Nat := 765334015195143968845399

theorem tailTrace_2235724 : CollatzResearch.WordTrace tailWord_2235724 prefixEnd_2235724 765334015195143968845399 := by
  unfold tailWord_2235724
  simp only [CollatzResearch.WordTrace]
  refine ⟨40771776676180627052585113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54362368901574169403446817 40771776676180627052585113)
  ·
    refine ⟨30578832507135470289438835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40771776676180627052585113 30578832507135470289438835)
    ·
      refine ⟨45868248760703205434158253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30578832507135470289438835 45868248760703205434158253)
      ·
        refine ⟨17200593285263702037809345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45868248760703205434158253 17200593285263702037809345)
        ·
          refine ⟨12900444963947776528357009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17200593285263702037809345 12900444963947776528357009)
          ·
            refine ⟨9675333722960832396267757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12900444963947776528357009 9675333722960832396267757)
            ·
              refine ⟨3628250146110312148600409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9675333722960832396267757 3628250146110312148600409)
              ·
                refine ⟨2721187609582734111450307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3628250146110312148600409 2721187609582734111450307)
                ·
                  refine ⟨4081781414374101167175461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2721187609582734111450307 4081781414374101167175461)
                  ·
                    refine ⟨765334015195143968845399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4081781414374101167175461 765334015195143968845399)
                    ·
                      rfl

theorem cell22_2235724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_2235724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235724 prefixEnd_2235724 := by exact prefixLift 2235724
  have htrace : WordTrace (prefixWord ++ tailWord_2235724) baseStart_2235724 baseEnd_2235724 := by
    simpa [prefixWord, tailWord_2235724, baseEnd_2235724] using wordTrace_append hprefix tailTrace_2235724
  have hstable : (prefixWord ++ tailWord_2235724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235724).length < 2 ^ (prefixWord ++ tailWord_2235724).sum := by decide
  have hdescent : baseEnd_2235724 < baseStart_2235724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235737 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 6, 3]
def baseStart_2235737 : Nat := 118140960795 + 2235737 * 2 ^ 59
def prefixEnd_2235737 : Nat := 4983230072969 + 3 ^ 40 * 2235737 * 2
def baseEnd_2235737 : Nat := 765338465360816268270359

theorem tailTrace_2235737 : CollatzResearch.WordTrace tailWord_2235737 prefixEnd_2235737 765338465360816268270359 := by
  unfold tailWord_2235737
  simp only [CollatzResearch.WordTrace]
  refine ⟨81544027501314157325393465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54362685000876104883595643 81544027501314157325393465)
  ·
    refine ⟨61158020625985617994045099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81544027501314157325393465 61158020625985617994045099)
    ·
      refine ⟨91737030938978426991067649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61158020625985617994045099 91737030938978426991067649)
      ·
        refine ⟨68802773204233820243300737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91737030938978426991067649 68802773204233820243300737)
        ·
          refine ⟨51602079903175365182475553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68802773204233820243300737 51602079903175365182475553)
          ·
            refine ⟨38701559927381523886856665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51602079903175365182475553 38701559927381523886856665)
            ·
              refine ⟨29026169945536142915142499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38701559927381523886856665 29026169945536142915142499)
              ·
                refine ⟨43539254918304214372713749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29026169945536142915142499 43539254918304214372713749)
                ·
                  refine ⟨2040902574295510048720957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43539254918304214372713749 2040902574295510048720957)
                  ·
                    refine ⟨765338465360816268270359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2040902574295510048720957 765338465360816268270359)
                    ·
                      rfl

theorem cell22_2235737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 3].length) (baseStart_2235737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235737 prefixEnd_2235737 := by exact prefixLift 2235737
  have htrace : WordTrace (prefixWord ++ tailWord_2235737) baseStart_2235737 baseEnd_2235737 := by
    simpa [prefixWord, tailWord_2235737, baseEnd_2235737] using wordTrace_append hprefix tailTrace_2235737
  have hstable : (prefixWord ++ tailWord_2235737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235737).length < 2 ^ (prefixWord ++ tailWord_2235737).sum := by decide
  have hdescent : baseEnd_2235737 < baseStart_2235737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235756 : List Nat := [2, 2, 1, 1, 5, 1, 4, 2, 4]
def baseStart_2235756 : Nat := 118140960795 + 2235756 * 2 ^ 59
def prefixEnd_2235756 : Nat := 4983230072969 + 3 ^ 40 * 2235756 * 2
def baseEnd_2235756 : Nat := 255114989816368850681767

theorem tailTrace_2235756 : CollatzResearch.WordTrace tailWord_2235756 prefixEnd_2235756 255114989816368850681767 := by
  unfold tailWord_2235756
  simp only [CollatzResearch.WordTrace]
  refine ⟨40772360244122661785167561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54363146992163549046890081 40772360244122661785167561)
  ·
    refine ⟨30579270183091996338875671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40772360244122661785167561 30579270183091996338875671)
    ·
      refine ⟨45868905274637994508313507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30579270183091996338875671 45868905274637994508313507)
      ·
        refine ⟨68803357911956991762470261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45868905274637994508313507 68803357911956991762470261)
        ·
          refine ⟨6450314804245967977731587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68803357911956991762470261 6450314804245967977731587)
          ·
            refine ⟨9675472206368951966597381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6450314804245967977731587 9675472206368951966597381)
            ·
              refine ⟨1814151038694178493737009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9675472206368951966597381 1814151038694178493737009)
              ·
                refine ⟨1360613279020633870302757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1814151038694178493737009 1360613279020633870302757)
                ·
                  refine ⟨255114989816368850681767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1360613279020633870302757 255114989816368850681767)
                  ·
                    rfl

theorem cell22_2235756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_2235756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235756 prefixEnd_2235756 := by exact prefixLift 2235756
  have htrace : WordTrace (prefixWord ++ tailWord_2235756) baseStart_2235756 baseEnd_2235756 := by
    simpa [prefixWord, tailWord_2235756, baseEnd_2235756] using wordTrace_append hprefix tailTrace_2235756
  have hstable : (prefixWord ++ tailWord_2235756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235756).length < 2 ^ (prefixWord ++ tailWord_2235756).sum := by decide
  have hdescent : baseEnd_2235756 < baseStart_2235756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235784 : List Nat := [2, 1, 3, 3, 1, 3, 3, 6]
def baseStart_2235784 : Nat := 118140960795 + 2235784 * 2 ^ 59
def prefixEnd_2235784 : Nat := 4983230072969 + 3 ^ 40 * 2235784 * 2
def baseEnd_2235784 : Nat := 85039394935702645816135

theorem tailTrace_2235784 : CollatzResearch.WordTrace tailWord_2235784 prefixEnd_2235784 85039394935702645816135 := by
  unfold tailWord_2235784
  simp only [CollatzResearch.WordTrace]
  refine ⟨40772870866071942176177203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54363827821429256234902937 40772870866071942176177203)
  ·
    refine ⟨61159306299107913264265805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40772870866071942176177203 61159306299107913264265805)
    ·
      refine ⟨22934739862165467474099677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61159306299107913264265805 22934739862165467474099677)
      ·
        refine ⟨8600527448312050302787379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22934739862165467474099677 8600527448312050302787379)
        ·
          refine ⟨12900791172468075454181069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8600527448312050302787379 12900791172468075454181069)
          ·
            refine ⟨4837796689675528295317901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12900791172468075454181069 4837796689675528295317901)
            ·
              refine ⟨1814173758628323110744213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4837796689675528295317901 1814173758628323110744213)
              ·
                refine ⟨85039394935702645816135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1814173758628323110744213 85039394935702645816135)
                ·
                  rfl

theorem cell22_2235784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 6].length) (baseStart_2235784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235784 prefixEnd_2235784 := by exact prefixLift 2235784
  have htrace : WordTrace (prefixWord ++ tailWord_2235784) baseStart_2235784 baseEnd_2235784 := by
    simpa [prefixWord, tailWord_2235784, baseEnd_2235784] using wordTrace_append hprefix tailTrace_2235784
  have hstable : (prefixWord ++ tailWord_2235784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235784).length < 2 ^ (prefixWord ++ tailWord_2235784).sum := by decide
  have hdescent : baseEnd_2235784 < baseStart_2235784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235872 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 5, 5]
def baseStart_2235872 : Nat := 118140960795 + 2235872 * 2 ^ 59
def prefixEnd_2235872 : Nat := 4983230072969 + 3 ^ 40 * 2235872 * 2
def baseEnd_2235872 : Nat := 765384678619720916144945

theorem tailTrace_2235872 : CollatzResearch.WordTrace tailWord_2235872 prefixEnd_2235872 765384678619720916144945 := by
  unfold tailWord_2235872
  simp only [CollatzResearch.WordTrace]
  refine ⟨40774475677912537690778935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54365967570550050254371913 40774475677912537690778935)
  ·
    refine ⟨61161713516868806536168403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40774475677912537690778935 61161713516868806536168403)
    ·
      refine ⟨91742570275303209804252605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61161713516868806536168403 91742570275303209804252605)
      ·
        refine ⟨34403463853238703676594727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91742570275303209804252605 34403463853238703676594727)
        ·
          refine ⟨51605195779858055514892091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34403463853238703676594727 51605195779858055514892091)
          ·
            refine ⟨77407793669787083272338137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51605195779858055514892091 77407793669787083272338137)
            ·
              refine ⟨58055845252340312454253603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77407793669787083272338137 58055845252340312454253603)
              ·
                refine ⟨87083767878510468681380405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58055845252340312454253603 87083767878510468681380405)
                ·
                  refine ⟨8164103238610356438879413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87083767878510468681380405 8164103238610356438879413)
                  ·
                    refine ⟨765384678619720916144945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8164103238610356438879413 765384678619720916144945)
                    ·
                      rfl

theorem cell22_2235872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_2235872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235872 prefixEnd_2235872 := by exact prefixLift 2235872
  have htrace : WordTrace (prefixWord ++ tailWord_2235872) baseStart_2235872 baseEnd_2235872 := by
    simpa [prefixWord, tailWord_2235872, baseEnd_2235872] using wordTrace_append hprefix tailTrace_2235872
  have hstable : (prefixWord ++ tailWord_2235872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235872).length < 2 ^ (prefixWord ++ tailWord_2235872).sum := by decide
  have hdescent : baseEnd_2235872 < baseStart_2235872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235887 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 3, 6]
def baseStart_2235887 : Nat := 118140960795 + 2235887 * 2 ^ 59
def prefixEnd_2235887 : Nat := 4983230072969 + 3 ^ 40 * 2235887 * 2
def baseEnd_2235887 : Nat := 765389813426265877019899

theorem tailTrace_2235887 : CollatzResearch.WordTrace tailWord_2235887 prefixEnd_2235887 765389813426265877019899 := by
  unfold tailWord_2235887
  simp only [CollatzResearch.WordTrace]
  refine ⟨81549498450770732943353915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54366332300513821962235943 81549498450770732943353915)
  ·
    refine ⟨122324247676156099415030873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81549498450770732943353915 122324247676156099415030873)
    ·
      refine ⟨91743185757117074561273155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122324247676156099415030873 91743185757117074561273155)
      ·
        refine ⟨137614778635675611841909733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91743185757117074561273155 137614778635675611841909733)
        ·
          refine ⟨25802770994189177220358075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137614778635675611841909733 25802770994189177220358075)
          ·
            refine ⟨38704156491283765830537113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25802770994189177220358075 38704156491283765830537113)
            ·
              refine ⟨29028117368462824372902835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38704156491283765830537113 29028117368462824372902835)
              ·
                refine ⟨43542176052694236559354253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29028117368462824372902835 43542176052694236559354253)
                ·
                  refine ⟨16328316019760338709757845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43542176052694236559354253 16328316019760338709757845)
                  ·
                    refine ⟨765389813426265877019899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16328316019760338709757845 765389813426265877019899)
                    ·
                      rfl

theorem cell22_2235887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_2235887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235887 prefixEnd_2235887 := by exact prefixLift 2235887
  have htrace : WordTrace (prefixWord ++ tailWord_2235887) baseStart_2235887 baseEnd_2235887 := by
    simpa [prefixWord, tailWord_2235887, baseEnd_2235887] using wordTrace_append hprefix tailTrace_2235887
  have hstable : (prefixWord ++ tailWord_2235887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235887).length < 2 ^ (prefixWord ++ tailWord_2235887).sum := by decide
  have hdescent : baseEnd_2235887 < baseStart_2235887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235893 : List Nat := [1, 3, 5, 1, 1, 1, 3, 2, 1, 4]
def baseStart_2235893 : Nat := 118140960795 + 2235893 * 2 ^ 59
def prefixEnd_2235893 : Nat := 4983230072969 + 3 ^ 40 * 2235893 * 2
def baseEnd_2235893 : Nat := 765391867348883861369881

theorem tailTrace_2235893 : CollatzResearch.WordTrace tailWord_2235893 prefixEnd_2235893 765391867348883861369881 := by
  unfold tailWord_2235893
  simp only [CollatzResearch.WordTrace]
  refine ⟨81549717288748995968072333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54366478192499330645381555 81549717288748995968072333)
  ·
    refine ⟨30581143983280873488027125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81549717288748995968072333 30581143983280873488027125)
    ·
      refine ⟨2866982248432581889502543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30581143983280873488027125 2866982248432581889502543)
      ·
        refine ⟨4300473372648872834253815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2866982248432581889502543 4300473372648872834253815)
        ·
          refine ⟨6450710058973309251380723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4300473372648872834253815 6450710058973309251380723)
          ·
            refine ⟨9676065088459963877071085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6450710058973309251380723 9676065088459963877071085)
            ·
              refine ⟨3628524408172486453901657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9676065088459963877071085 3628524408172486453901657)
              ·
                refine ⟨2721393306129364840426243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3628524408172486453901657 2721393306129364840426243)
                ·
                  refine ⟨4082089959194047260639365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2721393306129364840426243 4082089959194047260639365)
                  ·
                    refine ⟨765391867348883861369881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4082089959194047260639365 765391867348883861369881)
                    ·
                      rfl

theorem cell22_2235893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_2235893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235893 prefixEnd_2235893 := by exact prefixLift 2235893
  have htrace : WordTrace (prefixWord ++ tailWord_2235893) baseStart_2235893 baseEnd_2235893 := by
    simpa [prefixWord, tailWord_2235893, baseEnd_2235893] using wordTrace_append hprefix tailTrace_2235893
  have hstable : (prefixWord ++ tailWord_2235893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235893).length < 2 ^ (prefixWord ++ tailWord_2235893).sum := by decide
  have hdescent : baseEnd_2235893 < baseStart_2235893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235906 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_2235906 : Nat := 118140960795 + 2235906 * 2 ^ 59
def prefixEnd_2235906 : Nat := 4983230072969 + 3 ^ 40 * 2235906 * 2
def baseEnd_2235906 : Nat := 765396317514556160794841

theorem tailTrace_2235906 : CollatzResearch.WordTrace tailWord_2235906 prefixEnd_2235906 765396317514556160794841 := by
  unfold tailWord_2235906
  simp only [CollatzResearch.WordTrace]
  refine ⟨20387547859425474797073893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54366794291801266125530381 20387547859425474797073893)
  ·
    refine ⟨3822665223642276524451355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20387547859425474797073893 3822665223642276524451355)
    ·
      refine ⟨5733997835463414786677033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3822665223642276524451355 5733997835463414786677033)
      ·
        refine ⟨4300498376597561090007775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5733997835463414786677033 4300498376597561090007775)
        ·
          refine ⟨6450747564896341635011663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4300498376597561090007775 6450747564896341635011663)
          ·
            refine ⟨9676121347344512452517495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6450747564896341635011663 9676121347344512452517495)
            ·
              refine ⟨14514182021016768678776243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9676121347344512452517495 14514182021016768678776243)
              ·
                refine ⟨21771273031525153018164365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14514182021016768678776243 21771273031525153018164365)
                ·
                  refine ⟨8164227386821932381811637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21771273031525153018164365 8164227386821932381811637)
                  ·
                    refine ⟨765396317514556160794841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8164227386821932381811637 765396317514556160794841)
                    ·
                      rfl

theorem cell22_2235906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_2235906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235906 prefixEnd_2235906 := by exact prefixLift 2235906
  have htrace : WordTrace (prefixWord ++ tailWord_2235906) baseStart_2235906 baseEnd_2235906 := by
    simpa [prefixWord, tailWord_2235906, baseEnd_2235906] using wordTrace_append hprefix tailTrace_2235906
  have hstable : (prefixWord ++ tailWord_2235906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235906).length < 2 ^ (prefixWord ++ tailWord_2235906).sum := by decide
  have hdescent : baseEnd_2235906 < baseStart_2235906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235936 : List Nat := [2, 1, 1, 6, 1, 3, 1, 7]
def baseStart_2235936 : Nat := 118140960795 + 2235936 * 2 ^ 59
def prefixEnd_2235936 : Nat := 4983230072969 + 3 ^ 40 * 2235936 * 2
def baseEnd_2235936 : Nat := 85045176347516231393861

theorem tailTrace_2235936 : CollatzResearch.WordTrace tailWord_2235936 prefixEnd_2235936 85045176347516231393861 := by
  unfold tailWord_2235936
  simp only [CollatzResearch.WordTrace]
  refine ⟨40775642813796607155943831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54367523751728809541258441 40775642813796607155943831)
  ·
    refine ⟨61163464220694910733915747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40775642813796607155943831 61163464220694910733915747)
    ·
      refine ⟨91745196331042366100873621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61163464220694910733915747 91745196331042366100873621)
      ·
        refine ⟨4300556078017610910978451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 91745196331042366100873621 4300556078017610910978451)
        ·
          refine ⟨6450834117026416366467677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4300556078017610910978451 6450834117026416366467677)
          ·
            refine ⟨2419062793884906137425379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6450834117026416366467677 2419062793884906137425379)
            ·
              refine ⟨3628594190827359206138069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2419062793884906137425379 3628594190827359206138069)
              ·
                refine ⟨85045176347516231393861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3628594190827359206138069 85045176347516231393861)
                ·
                  rfl

theorem cell22_2235936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 7].length) (baseStart_2235936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235936 prefixEnd_2235936 := by exact prefixLift 2235936
  have htrace : WordTrace (prefixWord ++ tailWord_2235936) baseStart_2235936 baseEnd_2235936 := by
    simpa [prefixWord, tailWord_2235936, baseEnd_2235936] using wordTrace_append hprefix tailTrace_2235936
  have hstable : (prefixWord ++ tailWord_2235936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235936).length < 2 ^ (prefixWord ++ tailWord_2235936).sum := by decide
  have hdescent : baseEnd_2235936 < baseStart_2235936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235947 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 11]
def baseStart_2235947 : Nat := 118140960795 + 2235947 * 2 ^ 59
def prefixEnd_2235947 : Nat := 4983230072969 + 3 ^ 40 * 2235947 * 2
def baseEnd_2235947 : Nat := 255136784217481906839905

theorem tailTrace_2235947 : CollatzResearch.WordTrace tailWord_2235947 prefixEnd_2235947 255136784217481906839905 := by
  unfold tailWord_2235947
  simp only [CollatzResearch.WordTrace]
  refine ⟨81551686830553363190538095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54367791220368908793692063 81551686830553363190538095)
  ·
    refine ⟨122327530245830044785807143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81551686830553363190538095 122327530245830044785807143)
    ·
      refine ⟨183491295368745067178710715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122327530245830044785807143 183491295368745067178710715)
      ·
        refine ⟨275236943053117600768066073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183491295368745067178710715 275236943053117600768066073)
        ·
          refine ⟨206427707289838200576049555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275236943053117600768066073 206427707289838200576049555)
          ·
            refine ⟨309641560934757300864074333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206427707289838200576049555 309641560934757300864074333)
            ·
              refine ⟨116115585350533987824027875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 309641560934757300864074333 116115585350533987824027875)
              ·
                refine ⟨174173378025800981736041813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116115585350533987824027875 174173378025800981736041813)
                ·
                  refine ⟨255136784217481906839905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 174173378025800981736041813 255136784217481906839905)
                  ·
                    rfl

theorem cell22_2235947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 11].length) (baseStart_2235947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235947 prefixEnd_2235947 := by exact prefixLift 2235947
  have htrace : WordTrace (prefixWord ++ tailWord_2235947) baseStart_2235947 baseEnd_2235947 := by
    simpa [prefixWord, tailWord_2235947, baseEnd_2235947] using wordTrace_append hprefix tailTrace_2235947
  have hstable : (prefixWord ++ tailWord_2235947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235947).length < 2 ^ (prefixWord ++ tailWord_2235947).sum := by decide
  have hdescent : baseEnd_2235947 < baseStart_2235947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235974 : List Nat := [6, 1, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_2235974 : Nat := 118140960795 + 2235974 * 2 ^ 59
def prefixEnd_2235974 : Nat := 4983230072969 + 3 ^ 40 * 2235974 * 2
def baseEnd_2235974 : Nat := 765419595304226650094633

theorem tailTrace_2235974 : CollatzResearch.WordTrace tailWord_2235974 prefixEnd_2235974 765419595304226650094633 := by
  unfold tailWord_2235974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2548520987545485837555343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54368447734303697867847317 2548520987545485837555343)
  ·
    refine ⟨3822781481318228756333015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2548520987545485837555343 3822781481318228756333015)
    ·
      refine ⟨5734172221977343134499523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3822781481318228756333015 5734172221977343134499523)
      ·
        refine ⟨8601258332966014701749285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5734172221977343134499523 8601258332966014701749285)
        ·
          refine ⟨1612735937431127756577991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8601258332966014701749285 1612735937431127756577991)
          ·
            refine ⟨2419103906146691634866987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1612735937431127756577991 2419103906146691634866987)
            ·
              refine ⟨3628655859220037452300481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2419103906146691634866987 3628655859220037452300481)
              ·
                refine ⟨2721491894415028089225361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3628655859220037452300481 2721491894415028089225361)
                ·
                  refine ⟨2041118920811271066919021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2721491894415028089225361 2041118920811271066919021)
                  ·
                    refine ⟨765419595304226650094633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2041118920811271066919021 765419595304226650094633)
                    ·
                      rfl

theorem cell22_2235974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_2235974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235974 prefixEnd_2235974 := by exact prefixLift 2235974
  have htrace : WordTrace (prefixWord ++ tailWord_2235974) baseStart_2235974 baseEnd_2235974 := by
    simpa [prefixWord, tailWord_2235974, baseEnd_2235974] using wordTrace_append hprefix tailTrace_2235974
  have hstable : (prefixWord ++ tailWord_2235974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235974).length < 2 ^ (prefixWord ++ tailWord_2235974).sum := by decide
  have hdescent : baseEnd_2235974 < baseStart_2235974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235994 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 5, 4]
def baseStart_2235994 : Nat := 118140960795 + 2235994 * 2 ^ 59
def prefixEnd_2235994 : Nat := 4983230072969 + 3 ^ 40 * 2235994 * 2
def baseEnd_2235994 : Nat := 765426441712953264594571

theorem tailTrace_2235994 : CollatzResearch.WordTrace tailWord_2235994 prefixEnd_2235994 765426441712953264594571 := by
  unfold tailWord_2235994
  simp only [CollatzResearch.WordTrace]
  refine ⟨20388350265345772554374759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54368934040922060144999357 20388350265345772554374759)
  ·
    refine ⟨30582525398018658831562139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20388350265345772554374759 30582525398018658831562139)
    ·
      refine ⟨45873788097027988247343209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30582525398018658831562139 45873788097027988247343209)
      ·
        refine ⟨34405341072770991185507407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45873788097027988247343209 34405341072770991185507407)
        ·
          refine ⟨51608011609156486778261111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34405341072770991185507407 51608011609156486778261111)
          ·
            refine ⟨77412017413734730167391667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51608011609156486778261111 77412017413734730167391667)
            ·
              refine ⟨116118026120602095251087501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77412017413734730167391667 116118026120602095251087501)
              ·
                refine ⟨43544259795225785719157813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116118026120602095251087501 43544259795225785719157813)
                ·
                  refine ⟨4082274355802417411171045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43544259795225785719157813 4082274355802417411171045)
                  ·
                    refine ⟨765426441712953264594571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4082274355802417411171045 765426441712953264594571)
                    ·
                      rfl

theorem cell22_2235994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_2235994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235994 prefixEnd_2235994 := by exact prefixLift 2235994
  have htrace : WordTrace (prefixWord ++ tailWord_2235994) baseStart_2235994 baseEnd_2235994 := by
    simpa [prefixWord, tailWord_2235994, baseEnd_2235994] using wordTrace_append hprefix tailTrace_2235994
  have hstable : (prefixWord ++ tailWord_2235994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235994).length < 2 ^ (prefixWord ++ tailWord_2235994).sum := by decide
  have hdescent : baseEnd_2235994 < baseStart_2235994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2235996 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 2, 5]
def baseStart_2235996 : Nat := 118140960795 + 2235996 * 2 ^ 59
def prefixEnd_2235996 : Nat := 4983230072969 + 3 ^ 40 * 2235996 * 2
def baseEnd_2235996 : Nat := 765427126353825926044565

theorem tailTrace_2235996 : CollatzResearch.WordTrace tailWord_2235996 prefixEnd_2235996 765427126353825926044565 := by
  unfold tailWord_2235996
  simp only [CollatzResearch.WordTrace]
  refine ⟨40776737003687922279535921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54368982671583896372714561 40776737003687922279535921)
  ·
    refine ⟨30582552752765941709651941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40776737003687922279535921 30582552752765941709651941)
    ·
      refine ⟨5734228641143614070559739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30582552752765941709651941 5734228641143614070559739)
      ·
        refine ⟨8601342961715421105839609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5734228641143614070559739 8601342961715421105839609)
        ·
          refine ⟨6451007221286565829379707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8601342961715421105839609 6451007221286565829379707)
          ·
            refine ⟨9676510831929848744069561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6451007221286565829379707 9676510831929848744069561)
            ·
              refine ⟨7257383123947386558052171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9676510831929848744069561 7257383123947386558052171)
              ·
                refine ⟨10886074685921079837078257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7257383123947386558052171 10886074685921079837078257)
                ·
                  refine ⟨8164556014440809877808693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10886074685921079837078257 8164556014440809877808693)
                  ·
                    refine ⟨765427126353825926044565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8164556014440809877808693 765427126353825926044565)
                    ·
                      rfl

theorem cell22_2235996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_2235996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2235996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2235996 prefixEnd_2235996 := by exact prefixLift 2235996
  have htrace : WordTrace (prefixWord ++ tailWord_2235996) baseStart_2235996 baseEnd_2235996 := by
    simpa [prefixWord, tailWord_2235996, baseEnd_2235996] using wordTrace_append hprefix tailTrace_2235996
  have hstable : (prefixWord ++ tailWord_2235996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2235996).length < 2 ^ (prefixWord ++ tailWord_2235996).sum := by decide
  have hdescent : baseEnd_2235996 < baseStart_2235996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2235996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236009 : List Nat := [1, 2, 1, 1, 1, 4, 4, 2, 6]
def baseStart_2236009 : Nat := 118140960795 + 2236009 * 2 ^ 59
def prefixEnd_2236009 : Nat := 4983230072969 + 3 ^ 40 * 2236009 * 2
def baseEnd_2236009 : Nat := 255143858839832741823175

theorem tailTrace_2236009 : CollatzResearch.WordTrace tailWord_2236009 prefixEnd_2236009 255143858839832741823175 := by
  unfold tailWord_2236009
  simp only [CollatzResearch.WordTrace]
  refine ⟨81553948156328747779295081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54369298770885831852863387 81553948156328747779295081)
  ·
    refine ⟨61165461117246560834471311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81553948156328747779295081 61165461117246560834471311)
    ·
      refine ⟨91748191675869841251706967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61165461117246560834471311 91748191675869841251706967)
      ·
        refine ⟨137622287513804761877560451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91748191675869841251706967 137622287513804761877560451)
        ·
          refine ⟨206433431270707142816340677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137622287513804761877560451 206433431270707142816340677)
          ·
            refine ⟨38706268363257589278063877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206433431270707142816340677 38706268363257589278063877)
            ·
              refine ⟨7257425318110797989636977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38706268363257589278063877 7257425318110797989636977)
              ·
                refine ⟨5443068988583098492227733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7257425318110797989636977 5443068988583098492227733)
                ·
                  refine ⟨255143858839832741823175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5443068988583098492227733 255143858839832741823175)
                  ·
                    rfl

theorem cell22_2236009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 6].length) (baseStart_2236009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236009 prefixEnd_2236009 := by exact prefixLift 2236009
  have htrace : WordTrace (prefixWord ++ tailWord_2236009) baseStart_2236009 baseEnd_2236009 := by
    simpa [prefixWord, tailWord_2236009, baseEnd_2236009] using wordTrace_append hprefix tailTrace_2236009
  have hstable : (prefixWord ++ tailWord_2236009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236009).length < 2 ^ (prefixWord ++ tailWord_2236009).sum := by decide
  have hdescent : baseEnd_2236009 < baseStart_2236009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236026 : List Nat := [3, 1, 1, 1, 1, 1, 1, 9, 4]
def baseStart_2236026 : Nat := 118140960795 + 2236026 * 2 ^ 59
def prefixEnd_2236026 : Nat := 4983230072969 + 3 ^ 40 * 2236026 * 2
def baseEnd_2236026 : Nat := 255145798655638615931491

theorem tailTrace_2236026 : CollatzResearch.WordTrace tailWord_2236026 prefixEnd_2236026 255145798655638615931491 := by
  unfold tailWord_2236026
  simp only [CollatzResearch.WordTrace]
  refine ⟨20388642049316789920665983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54369712131511439788442621 20388642049316789920665983)
  ·
    refine ⟨30582963073975184880998975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20388642049316789920665983 30582963073975184880998975)
    ·
      refine ⟨45874444610962777321498463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30582963073975184880998975 45874444610962777321498463)
      ·
        refine ⟨68811666916444165982247695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45874444610962777321498463 68811666916444165982247695)
        ·
          refine ⟨103217500374666248973371543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68811666916444165982247695 103217500374666248973371543)
          ·
            refine ⟨154826250561999373460057315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103217500374666248973371543 154826250561999373460057315)
            ·
              refine ⟨232239375842999060190085973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154826250561999373460057315 232239375842999060190085973)
              ·
                refine ⟨1360777592830072618301285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 232239375842999060190085973 1360777592830072618301285)
                ·
                  refine ⟨255145798655638615931491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1360777592830072618301285 255145798655638615931491)
                  ·
                    rfl

theorem cell22_2236026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_2236026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236026 prefixEnd_2236026 := by exact prefixLift 2236026
  have htrace : WordTrace (prefixWord ++ tailWord_2236026) baseStart_2236026 baseEnd_2236026 := by
    simpa [prefixWord, tailWord_2236026, baseEnd_2236026] using wordTrace_append hprefix tailTrace_2236026
  have hstable : (prefixWord ++ tailWord_2236026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236026).length < 2 ^ (prefixWord ++ tailWord_2236026).sum := by decide
  have hdescent : baseEnd_2236026 < baseStart_2236026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236041 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 4, 3]
def baseStart_2236041 : Nat := 118140960795 + 2236041 * 2 ^ 59
def prefixEnd_2236041 : Nat := 4983230072969 + 3 ^ 40 * 2236041 * 2
def baseEnd_2236041 : Nat := 765442530773460808669427

theorem tailTrace_2236041 : CollatzResearch.WordTrace tailWord_2236041 prefixEnd_2236041 765442530773460808669427 := by
  unfold tailWord_2236041
  simp only [CollatzResearch.WordTrace]
  refine ⟨81555115292212817244459977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54370076861475211496306651 81555115292212817244459977)
  ·
    refine ⟨61166336469159612933344983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81555115292212817244459977 61166336469159612933344983)
    ·
      refine ⟨91749504703739419400017475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61166336469159612933344983 91749504703739419400017475)
      ·
        refine ⟨137624257055609129100026213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91749504703739419400017475 137624257055609129100026213)
        ·
          refine ⟨25804548197926711706254915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137624257055609129100026213 25804548197926711706254915)
          ·
            refine ⟨38706822296890067559382373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25804548197926711706254915 38706822296890067559382373)
            ·
              refine ⟨7257529180666887667384195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38706822296890067559382373 7257529180666887667384195)
              ·
                refine ⟨10886293771000331501076293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7257529180666887667384195 10886293771000331501076293)
                ·
                  refine ⟨2041180082062562156451805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10886293771000331501076293 2041180082062562156451805)
                  ·
                    refine ⟨765442530773460808669427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2041180082062562156451805 765442530773460808669427)
                    ·
                      rfl

theorem cell22_2236041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 3].length) (baseStart_2236041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236041 prefixEnd_2236041 := by exact prefixLift 2236041
  have htrace : WordTrace (prefixWord ++ tailWord_2236041) baseStart_2236041 baseEnd_2236041 := by
    simpa [prefixWord, tailWord_2236041, baseEnd_2236041] using wordTrace_append hprefix tailTrace_2236041
  have hstable : (prefixWord ++ tailWord_2236041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236041).length < 2 ^ (prefixWord ++ tailWord_2236041).sum := by decide
  have hdescent : baseEnd_2236041 < baseStart_2236041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236043 : List Nat := [1, 1, 1, 1, 4, 1, 7, 2, 4]
def baseStart_2236043 : Nat := 118140960795 + 2236043 * 2 ^ 59
def prefixEnd_2236043 : Nat := 4983230072969 + 3 ^ 40 * 2236043 * 2
def baseEnd_2236043 : Nat := 255147738471444490039807

theorem tailTrace_2236043 : CollatzResearch.WordTrace tailWord_2236043 prefixEnd_2236043 255147738471444490039807 := by
  unfold tailWord_2236043
  simp only [CollatzResearch.WordTrace]
  refine ⟨81555188238205571586032783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54370125492137047724021855 81555188238205571586032783)
  ·
    refine ⟨122332782357308357379049175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81555188238205571586032783 122332782357308357379049175)
    ·
      refine ⟨183499173535962536068573763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122332782357308357379049175 183499173535962536068573763)
      ·
        refine ⟨275248760303943804102860645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183499173535962536068573763 275248760303943804102860645)
        ·
          refine ⟨51609142556989463269286371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 275248760303943804102860645 51609142556989463269286371)
          ·
            refine ⟨77413713835484194903929557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51609142556989463269286371 77413713835484194903929557)
            ·
              refine ⟨1814383918019160818060849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 77413713835484194903929557 1814383918019160818060849)
              ·
                refine ⟨1360787938514370613545637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1814383918019160818060849 1360787938514370613545637)
                ·
                  refine ⟨255147738471444490039807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1360787938514370613545637 255147738471444490039807)
                  ·
                    rfl

theorem cell22_2236043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 4].length) (baseStart_2236043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236043 prefixEnd_2236043 := by exact prefixLift 2236043
  have htrace : WordTrace (prefixWord ++ tailWord_2236043) baseStart_2236043 baseEnd_2236043 := by
    simpa [prefixWord, tailWord_2236043, baseEnd_2236043] using wordTrace_append hprefix tailTrace_2236043
  have hstable : (prefixWord ++ tailWord_2236043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236043).length < 2 ^ (prefixWord ++ tailWord_2236043).sum := by decide
  have hdescent : baseEnd_2236043 < baseStart_2236043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236069 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 2, 7]
def baseStart_2236069 : Nat := 118140960795 + 2236069 * 2 ^ 59
def prefixEnd_2236069 : Nat := 4983230072969 + 3 ^ 40 * 2236069 * 2
def baseEnd_2236069 : Nat := 765452115745678068969341

theorem tailTrace_2236069 : CollatzResearch.WordTrace tailWord_2236069 prefixEnd_2236069 765452115745678068969341 := by
  unfold tailWord_2236069
  simp only [CollatzResearch.WordTrace]
  refine ⟨81556136536111378026479261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54370757690740918684319507 81556136536111378026479261)
  ·
    refine ⟨30583551201041766759929723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81556136536111378026479261 30583551201041766759929723)
    ·
      refine ⟨45875326801562650139894585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30583551201041766759929723 45875326801562650139894585)
      ·
        refine ⟨34406495101171987604920939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45875326801562650139894585 34406495101171987604920939)
        ·
          refine ⟨51609742651757981407381409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34406495101171987604920939 51609742651757981407381409)
          ·
            refine ⟨38707306988818486055536057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51609742651757981407381409 38707306988818486055536057)
            ·
              refine ⟨29030480241613864541652043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38707306988818486055536057 29030480241613864541652043)
              ·
                refine ⟨43545720362420796812478065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29030480241613864541652043 43545720362420796812478065)
                ·
                  refine ⟨32659290271815597609358549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43545720362420796812478065 32659290271815597609358549)
                  ·
                    refine ⟨765452115745678068969341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32659290271815597609358549 765452115745678068969341)
                    ·
                      rfl

theorem cell22_2236069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_2236069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236069 prefixEnd_2236069 := by exact prefixLift 2236069
  have htrace : WordTrace (prefixWord ++ tailWord_2236069) baseStart_2236069 baseEnd_2236069 := by
    simpa [prefixWord, tailWord_2236069, baseEnd_2236069] using wordTrace_append hprefix tailTrace_2236069
  have hstable : (prefixWord ++ tailWord_2236069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236069).length < 2 ^ (prefixWord ++ tailWord_2236069).sum := by decide
  have hdescent : baseEnd_2236069 < baseStart_2236069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236150 : List Nat := [5, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_2236150 : Nat := 118140960795 + 2236150 * 2 ^ 59
def prefixEnd_2236150 : Nat := 4983230072969 + 3 ^ 40 * 2236150 * 2
def baseEnd_2236150 : Nat := 255159947900340285898031

theorem tailTrace_2236150 : CollatzResearch.WordTrace tailWord_2236150 prefixEnd_2236150 255159947900340285898031 := by
  unfold tailWord_2236150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5097443178051120553761119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54372727232545285906785269 5097443178051120553761119)
  ·
    refine ⟨7646164767076680830641679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5097443178051120553761119 7646164767076680830641679)
    ·
      refine ⟨11469247150615021245962519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7646164767076680830641679 11469247150615021245962519)
      ·
        refine ⟨17203870725922531868943779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11469247150615021245962519 17203870725922531868943779)
        ·
          refine ⟨25805806088883797803415669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17203870725922531868943779 25805806088883797803415669)
          ·
            refine ⟨2419294320832856044070219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25805806088883797803415669 2419294320832856044070219)
            ·
              refine ⟨3628941481249284066105329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2419294320832856044070219 3628941481249284066105329)
              ·
                refine ⟨2721706110936963049578997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3628941481249284066105329 2721706110936963049578997)
                ·
                  refine ⟨255159947900340285898031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2721706110936963049578997 255159947900340285898031)
                  ·
                    rfl

theorem cell22_2236150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_2236150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236150 prefixEnd_2236150 := by exact prefixLift 2236150
  have htrace : WordTrace (prefixWord ++ tailWord_2236150) baseStart_2236150 baseEnd_2236150 := by
    simpa [prefixWord, tailWord_2236150, baseEnd_2236150] using wordTrace_append hprefix tailTrace_2236150
  have hstable : (prefixWord ++ tailWord_2236150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236150).length < 2 ^ (prefixWord ++ tailWord_2236150).sum := by decide
  have hdescent : baseEnd_2236150 < baseStart_2236150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236161 : List Nat := [1, 2, 4, 1, 1, 1, 3, 3, 6]
def baseStart_2236161 : Nat := 118140960795 + 2236161 * 2 ^ 59
def prefixEnd_2236161 : Nat := 4983230072969 + 3 ^ 40 * 2236161 * 2
def baseEnd_2236161 : Nat := 255161203075273498556353

theorem tailTrace_2236161 : CollatzResearch.WordTrace tailWord_2236161 prefixEnd_2236161 255161203075273498556353 := by
  unfold tailWord_2236161
  simp only [CollatzResearch.WordTrace]
  refine ⟨81559492051778077738828337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54372994701185385159218891 81559492051778077738828337)
  ·
    refine ⟨61169619038833558304121253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81559492051778077738828337 61169619038833558304121253)
    ·
      refine ⟨11469303569781292182022735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61169619038833558304121253 11469303569781292182022735)
      ·
        refine ⟨17203955354671938273034103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11469303569781292182022735 17203955354671938273034103)
        ·
          refine ⟨25805933032007907409551155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17203955354671938273034103 25805933032007907409551155)
          ·
            refine ⟨38708899548011861114326733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25805933032007907409551155 38708899548011861114326733)
            ·
              refine ⟨14515837330504447917872525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38708899548011861114326733 14515837330504447917872525)
              ·
                refine ⟨5443438998939167969202197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14515837330504447917872525 5443438998939167969202197)
                ·
                  refine ⟨255161203075273498556353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5443438998939167969202197 255161203075273498556353)
                  ·
                    rfl

theorem cell22_2236161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 6].length) (baseStart_2236161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236161 prefixEnd_2236161 := by exact prefixLift 2236161
  have htrace : WordTrace (prefixWord ++ tailWord_2236161) baseStart_2236161 baseEnd_2236161 := by
    simpa [prefixWord, tailWord_2236161, baseEnd_2236161] using wordTrace_append hprefix tailTrace_2236161
  have hstable : (prefixWord ++ tailWord_2236161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236161).length < 2 ^ (prefixWord ++ tailWord_2236161).sum := by decide
  have hdescent : baseEnd_2236161 < baseStart_2236161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236191 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 1, 6]
def baseStart_2236191 : Nat := 118140960795 + 2236191 * 2 ^ 59
def prefixEnd_2236191 : Nat := 4983230072969 + 3 ^ 40 * 2236191 * 2
def baseEnd_2236191 : Nat := 765493878838910417418967

theorem tailTrace_2236191 : CollatzResearch.WordTrace tailWord_2236191 prefixEnd_2236191 765493878838910417418967 := by
  unfold tailWord_2236191
  simp only [CollatzResearch.WordTrace]
  refine ⟨81560586241669392862420427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54373724161112928574946951 81560586241669392862420427)
  ·
    refine ⟨122340879362504089293630641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81560586241669392862420427 122340879362504089293630641)
    ·
      refine ⟨91755659521878066970222981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122340879362504089293630641 91755659521878066970222981)
      ·
        refine ⟨17204186160352137556916809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91755659521878066970222981 17204186160352137556916809)
        ·
          refine ⟨12903139620264103167687607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17204186160352137556916809 12903139620264103167687607)
          ·
            refine ⟨19354709430396154751531411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12903139620264103167687607 19354709430396154751531411)
            ·
              refine ⟨29032064145594232127297117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19354709430396154751531411 29032064145594232127297117)
              ·
                refine ⟨10887024054597837047736419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29032064145594232127297117 10887024054597837047736419)
                ·
                  refine ⟨16330536081896755571604629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10887024054597837047736419 16330536081896755571604629)
                  ·
                    refine ⟨765493878838910417418967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16330536081896755571604629 765493878838910417418967)
                    ·
                      rfl

theorem cell22_2236191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_2236191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236191 prefixEnd_2236191 := by exact prefixLift 2236191
  have htrace : WordTrace (prefixWord ++ tailWord_2236191) baseStart_2236191 baseEnd_2236191 := by
    simpa [prefixWord, tailWord_2236191, baseEnd_2236191] using wordTrace_append hprefix tailTrace_2236191
  have hstable : (prefixWord ++ tailWord_2236191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236191).length < 2 ^ (prefixWord ++ tailWord_2236191).sum := by decide
  have hdescent : baseEnd_2236191 < baseStart_2236191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236193 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 4, 3]
def baseStart_2236193 : Nat := 118140960795 + 2236193 * 2 ^ 59
def prefixEnd_2236193 : Nat := 4983230072969 + 3 ^ 40 * 2236193 * 2
def baseEnd_2236193 : Nat := 765494563479783078868961

theorem tailTrace_2236193 : CollatzResearch.WordTrace tailWord_2236193 prefixEnd_2236193 765494563479783078868961 := by
  unfold tailWord_2236193
  simp only [CollatzResearch.WordTrace]
  refine ⟨81560659187662147203993233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54373772791774764802662155 81560659187662147203993233)
  ·
    refine ⟨61170494390746610402994925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81560659187662147203993233 61170494390746610402994925)
    ·
      refine ⟨22938935396529978901123097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61170494390746610402994925 22938935396529978901123097)
      ·
        refine ⟨17204201547397484175842323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22938935396529978901123097 17204201547397484175842323)
        ·
          refine ⟨25806302321096226263763485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17204201547397484175842323 25806302321096226263763485)
          ·
            refine ⟨9677363370411084848911307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25806302321096226263763485 9677363370411084848911307)
            ·
              refine ⟨14516045055616627273366961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9677363370411084848911307 14516045055616627273366961)
              ·
                refine ⟨10887033791712470455025221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14516045055616627273366961 10887033791712470455025221)
                ·
                  refine ⟨2041318835946088210317229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10887033791712470455025221 2041318835946088210317229)
                  ·
                    refine ⟨765494563479783078868961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2041318835946088210317229 765494563479783078868961)
                    ·
                      rfl

theorem cell22_2236193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_2236193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236193 prefixEnd_2236193 := by exact prefixLift 2236193
  have htrace : WordTrace (prefixWord ++ tailWord_2236193) baseStart_2236193 baseEnd_2236193 := by
    simpa [prefixWord, tailWord_2236193, baseEnd_2236193] using wordTrace_append hprefix tailTrace_2236193
  have hstable : (prefixWord ++ tailWord_2236193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236193).length < 2 ^ (prefixWord ++ tailWord_2236193).sum := by decide
  have hdescent : baseEnd_2236193 < baseStart_2236193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236223 : List Nat := [1, 1, 2, 2, 6, 1, 2, 7]
def baseStart_2236223 : Nat := 118140960795 + 2236223 * 2 ^ 59
def prefixEnd_2236223 : Nat := 4983230072969 + 3 ^ 40 * 2236223 * 2
def baseEnd_2236223 : Nat := 85056092565874777846541

theorem tailTrace_2236223 : CollatzResearch.WordTrace tailWord_2236223 prefixEnd_2236223 85056092565874777846541 := by
  unfold tailWord_2236223
  simp only [CollatzResearch.WordTrace]
  refine ⟨81561753377553462327585323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54374502251702308218390215 81561753377553462327585323)
  ·
    refine ⟨122342630066330193491377985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81561753377553462327585323 122342630066330193491377985)
    ·
      refine ⟨91756972549747645118533489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122342630066330193491377985 91756972549747645118533489)
      ·
        refine ⟨68817729412310733838900117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91756972549747645118533489 68817729412310733838900117)
        ·
          refine ⟨3225831066202065648698443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 68817729412310733838900117 3225831066202065648698443)
          ·
            refine ⟨4838746599303098473047665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3225831066202065648698443 4838746599303098473047665)
            ·
              refine ⟨3629059949477323854785749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4838746599303098473047665 3629059949477323854785749)
              ·
                refine ⟨85056092565874777846541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3629059949477323854785749 85056092565874777846541)
                ·
                  rfl

theorem cell22_2236223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 7].length) (baseStart_2236223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236223 prefixEnd_2236223 := by exact prefixLift 2236223
  have htrace : WordTrace (prefixWord ++ tailWord_2236223) baseStart_2236223 baseEnd_2236223 := by
    simpa [prefixWord, tailWord_2236223, baseEnd_2236223] using wordTrace_append hprefix tailTrace_2236223
  have hstable : (prefixWord ++ tailWord_2236223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236223).length < 2 ^ (prefixWord ++ tailWord_2236223).sum := by decide
  have hdescent : baseEnd_2236223 < baseStart_2236223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236227 : List Nat := [1, 1, 1, 3, 1, 7, 2, 1, 2, 3]
def baseStart_2236227 : Nat := 118140960795 + 2236227 * 2 ^ 59
def prefixEnd_2236227 : Nat := 4983230072969 + 3 ^ 40 * 2236227 * 2
def baseEnd_2236227 : Nat := 765506202374618323518857

theorem tailTrace_2236227 : CollatzResearch.WordTrace tailWord_2236227 prefixEnd_2236227 765506202374618323518857 := by
  unfold tailWord_2236227
  simp only [CollatzResearch.WordTrace]
  refine ⟨81561899269538971010730935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54374599513025980673820623 81561899269538971010730935)
  ·
    refine ⟨122342848904308456516096403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81561899269538971010730935 122342848904308456516096403)
    ·
      refine ⟨183514273356462684774144605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122342848904308456516096403 183514273356462684774144605)
      ·
        refine ⟨68817852508673506790304227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183514273356462684774144605 68817852508673506790304227)
        ·
          refine ⟨103226778763010260185456341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68817852508673506790304227 103226778763010260185456341)
          ·
            refine ⟨2419377627258052973096633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 103226778763010260185456341 2419377627258052973096633)
            ·
              refine ⟨1814533220443539729822475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2419377627258052973096633 1814533220443539729822475)
              ·
                refine ⟨2721799830665309594733713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1814533220443539729822475 2721799830665309594733713)
                ·
                  refine ⟨2041349872998982196050285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2721799830665309594733713 2041349872998982196050285)
                  ·
                    refine ⟨765506202374618323518857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2041349872998982196050285 765506202374618323518857)
                    ·
                      rfl

theorem cell22_2236227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 2, 3].length) (baseStart_2236227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236227 prefixEnd_2236227 := by exact prefixLift 2236227
  have htrace : WordTrace (prefixWord ++ tailWord_2236227) baseStart_2236227 baseEnd_2236227 := by
    simpa [prefixWord, tailWord_2236227, baseEnd_2236227] using wordTrace_append hprefix tailTrace_2236227
  have hstable : (prefixWord ++ tailWord_2236227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236227).length < 2 ^ (prefixWord ++ tailWord_2236227).sum := by decide
  have hdescent : baseEnd_2236227 < baseStart_2236227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236268 : List Nat := [2, 2, 1, 1, 4, 2, 1, 4, 5]
def baseStart_2236268 : Nat := 118140960795 + 2236268 * 2 ^ 59
def prefixEnd_2236268 : Nat := 4983230072969 + 3 ^ 40 * 2236268 * 2
def baseEnd_2236268 : Nat := 255173412504169294414577

theorem tailTrace_2236268 : CollatzResearch.WordTrace tailWord_2236268 prefixEnd_2236268 255173412504169294414577 := by
  unfold tailWord_2236268
  simp only [CollatzResearch.WordTrace]
  refine ⟨40781697331195217506486729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54375596441593623341982305 40781697331195217506486729)
  ·
    refine ⟨30586272998396413129865047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40781697331195217506486729 30586272998396413129865047)
    ·
      refine ⟨45879409497594619694797571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30586272998396413129865047 45879409497594619694797571)
      ·
        refine ⟨68819114246391929542196357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45879409497594619694797571 68819114246391929542196357)
        ·
          refine ⟨12903583921198486789161817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68819114246391929542196357 12903583921198486789161817)
          ·
            refine ⟨9677687940898865091871363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12903583921198486789161817 9677687940898865091871363)
            ·
              refine ⟨14516531911348297637807045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9677687940898865091871363 14516531911348297637807045)
              ·
                refine ⟨2721849733377805807088821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14516531911348297637807045 2721849733377805807088821)
                ·
                  refine ⟨255173412504169294414577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2721849733377805807088821 255173412504169294414577)
                  ·
                    rfl

theorem cell22_2236268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_2236268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236268 prefixEnd_2236268 := by exact prefixLift 2236268
  have htrace : WordTrace (prefixWord ++ tailWord_2236268) baseStart_2236268 baseEnd_2236268 := by
    simpa [prefixWord, tailWord_2236268, baseEnd_2236268] using wordTrace_append hprefix tailTrace_2236268
  have hstable : (prefixWord ++ tailWord_2236268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236268).length < 2 ^ (prefixWord ++ tailWord_2236268).sum := by decide
  have hdescent : baseEnd_2236268 < baseStart_2236268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236388 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_2236388 : Nat := 118140960795 + 2236388 * 2 ^ 59
def prefixEnd_2236388 : Nat := 4983230072969 + 3 ^ 40 * 2236388 * 2
def baseEnd_2236388 : Nat := 765561315964867570243363

theorem tailTrace_2236388 : CollatzResearch.WordTrace tailWord_2236388 prefixEnd_2236388 765561315964867570243363 := by
  unfold tailWord_2236388
  simp only [CollatzResearch.WordTrace]
  refine ⟨40783885710977847753670909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54378514281303797004894545 40783885710977847753670909)
  ·
    refine ⟨15293957141616692907626591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40783885710977847753670909 15293957141616692907626591)
    ·
      refine ⟨22940935712425039361439887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15293957141616692907626591 22940935712425039361439887)
      ·
        refine ⟨34411403568637559042159831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22940935712425039361439887 34411403568637559042159831)
        ·
          refine ⟨51617105352956338563239747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34411403568637559042159831 51617105352956338563239747)
          ·
            refine ⟨77425658029434507844859621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51617105352956338563239747 77425658029434507844859621)
            ·
              refine ⟨14517310880518970220911179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77425658029434507844859621 14517310880518970220911179)
              ·
                refine ⟨21775966320778455331366769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14517310880518970220911179 21775966320778455331366769)
                ·
                  refine ⟨16331974740583841498525077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21775966320778455331366769 16331974740583841498525077)
                  ·
                    refine ⟨765561315964867570243363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16331974740583841498525077 765561315964867570243363)
                    ·
                      rfl

theorem cell22_2236388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_2236388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236388 prefixEnd_2236388 := by exact prefixLift 2236388
  have htrace : WordTrace (prefixWord ++ tailWord_2236388) baseStart_2236388 baseEnd_2236388 := by
    simpa [prefixWord, tailWord_2236388, baseEnd_2236388] using wordTrace_append hprefix tailTrace_2236388
  have hstable : (prefixWord ++ tailWord_2236388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236388).length < 2 ^ (prefixWord ++ tailWord_2236388).sum := by decide
  have hdescent : baseEnd_2236388 < baseStart_2236388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236437 : List Nat := [1, 3, 2, 1, 5, 1, 2, 2, 5]
def baseStart_2236437 : Nat := 118140960795 + 2236437 * 2 ^ 59
def prefixEnd_2236437 : Nat := 4983230072969 + 3 ^ 40 * 2236437 * 2
def baseEnd_2236437 : Nat := 255192696555415925256071

theorem tailTrace_2236437 : CollatzResearch.WordTrace tailWord_2236437 prefixEnd_2236437 255192696555415925256071 := by
  unfold tailWord_2236437
  simp only [CollatzResearch.WordTrace]
  refine ⟨81569558598778176875875565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54379705732518784583917043 81569558598778176875875565)
  ·
    refine ⟨30588584474541816328453337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81569558598778176875875565 30588584474541816328453337)
    ·
      refine ⟨22941438355906362246340003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30588584474541816328453337 22941438355906362246340003)
      ·
        refine ⟨34412157533859543369510005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22941438355906362246340003 34412157533859543369510005)
        ·
          refine ⟨3226139768799332190891563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34412157533859543369510005 3226139768799332190891563)
          ·
            refine ⟨4839209653198998286337345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3226139768799332190891563 4839209653198998286337345)
            ·
              refine ⟨3629407239899248714753009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4839209653198998286337345 3629407239899248714753009)
              ·
                refine ⟨2722055429924436536064757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3629407239899248714753009 2722055429924436536064757)
                ·
                  refine ⟨255192696555415925256071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2722055429924436536064757 255192696555415925256071)
                  ·
                    rfl

theorem cell22_2236437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_2236437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236437 prefixEnd_2236437 := by exact prefixLift 2236437
  have htrace : WordTrace (prefixWord ++ tailWord_2236437) baseStart_2236437 baseEnd_2236437 := by
    simpa [prefixWord, tailWord_2236437, baseEnd_2236437] using wordTrace_append hprefix tailTrace_2236437
  have hstable : (prefixWord ++ tailWord_2236437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236437).length < 2 ^ (prefixWord ++ tailWord_2236437).sum := by decide
  have hdescent : baseEnd_2236437 < baseStart_2236437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236450 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_2236450 : Nat := 118140960795 + 2236450 * 2 ^ 59
def prefixEnd_2236450 : Nat := 4983230072969 + 3 ^ 40 * 2236450 * 2
def baseEnd_2236450 : Nat := 765582539831920075193173

theorem tailTrace_2236450 : CollatzResearch.WordTrace tailWord_2236450 prefixEnd_2236450 765582539831920075193173 := by
  unfold tailWord_2236450
  simp only [CollatzResearch.WordTrace]
  refine ⟨20392508186932770024024701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54380021831820720064065869 20392508186932770024024701)
  ·
    refine ⟨7647190570099788759009263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20392508186932770024024701 7647190570099788759009263)
    ·
      refine ⟨11470785855149683138513895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7647190570099788759009263 11470785855149683138513895)
      ·
        refine ⟨17206178782724524707770843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11470785855149683138513895 17206178782724524707770843)
        ·
          refine ⟨25809268174086787061656265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17206178782724524707770843 25809268174086787061656265)
          ·
            refine ⟨19356951130565090296242199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25809268174086787061656265 19356951130565090296242199)
            ·
              refine ⟨29035426695847635444363299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19356951130565090296242199 29035426695847635444363299)
              ·
                refine ⟨43553140043771453166544949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29035426695847635444363299 43553140043771453166544949)
                ·
                  refine ⟨4083106879103573734363589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43553140043771453166544949 4083106879103573734363589)
                  ·
                    refine ⟨765582539831920075193173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4083106879103573734363589 765582539831920075193173)
                    ·
                      rfl

theorem cell22_2236450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_2236450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236450 prefixEnd_2236450 := by exact prefixLift 2236450
  have htrace : WordTrace (prefixWord ++ tailWord_2236450) baseStart_2236450 baseEnd_2236450 := by
    simpa [prefixWord, tailWord_2236450, baseEnd_2236450] using wordTrace_append hprefix tailTrace_2236450
  have hstable : (prefixWord ++ tailWord_2236450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236450).length < 2 ^ (prefixWord ++ tailWord_2236450).sum := by decide
  have hdescent : baseEnd_2236450 < baseStart_2236450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236452 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_2236452 : Nat := 118140960795 + 2236452 * 2 ^ 59
def prefixEnd_2236452 : Nat := 4983230072969 + 3 ^ 40 * 2236452 * 2
def baseEnd_2236452 : Nat := 765583224472792736643167

theorem tailTrace_2236452 : CollatzResearch.WordTrace tailWord_2236452 prefixEnd_2236452 765583224472792736643167 := by
  unfold tailWord_2236452
  simp only [CollatzResearch.WordTrace]
  refine ⟨40785052846861917218835805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54380070462482556291781073 40785052846861917218835805)
  ·
    refine ⟨15294394817573218957063427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40785052846861917218835805 15294394817573218957063427)
    ·
      refine ⟨22941592226359828435595141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15294394817573218957063427 22941592226359828435595141)
      ·
        refine ⟨4301548542442467831674089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22941592226359828435595141 4301548542442467831674089)
        ·
          refine ⟨3226161406831850873755567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4301548542442467831674089 3226161406831850873755567)
          ·
            refine ⟨4839242110247776310633351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3226161406831850873755567 4839242110247776310633351)
            ·
              refine ⟨7258863165371664465950027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4839242110247776310633351 7258863165371664465950027)
              ·
                refine ⟨10888294748057496698925041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7258863165371664465950027 10888294748057496698925041)
                ·
                  refine ⟨8166221061043122524193781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10888294748057496698925041 8166221061043122524193781)
                  ·
                    refine ⟨765583224472792736643167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8166221061043122524193781 765583224472792736643167)
                    ·
                      rfl

theorem cell22_2236452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_2236452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236452 prefixEnd_2236452 := by exact prefixLift 2236452
  have htrace : WordTrace (prefixWord ++ tailWord_2236452) baseStart_2236452 baseEnd_2236452 := by
    simpa [prefixWord, tailWord_2236452, baseEnd_2236452] using wordTrace_append hprefix tailTrace_2236452
  have hstable : (prefixWord ++ tailWord_2236452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236452).length < 2 ^ (prefixWord ++ tailWord_2236452).sum := by decide
  have hdescent : baseEnd_2236452 < baseStart_2236452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236465 : List Nat := [1, 2, 2, 3, 1, 4, 1, 2, 6]
def baseStart_2236465 : Nat := 118140960795 + 2236465 * 2 ^ 59
def prefixEnd_2236465 : Nat := 4983230072969 + 3 ^ 40 * 2236465 * 2
def baseEnd_2236465 : Nat := 255195891546155012022709

theorem tailTrace_2236465 : CollatzResearch.WordTrace tailWord_2236465 prefixEnd_2236465 255195891546155012022709 := by
  unfold tailWord_2236465
  simp only [CollatzResearch.WordTrace]
  refine ⟨81570579842676737657894849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54380386561784491771929899 81570579842676737657894849)
  ·
    refine ⟨61177934882007553243421137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81570579842676737657894849 61177934882007553243421137)
    ·
      refine ⟨45883451161505664932565853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61177934882007553243421137 45883451161505664932565853)
      ·
        refine ⟨17206294185564624349712195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45883451161505664932565853 17206294185564624349712195)
        ·
          refine ⟨25809441278346936524568293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17206294185564624349712195 25809441278346936524568293)
          ·
            refine ⟨4839270239690050598356555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25809441278346936524568293 4839270239690050598356555)
            ·
              refine ⟨7258905359535075897534833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4839270239690050598356555 7258905359535075897534833)
              ·
                refine ⟨5444179019651306923151125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7258905359535075897534833 5444179019651306923151125)
                ·
                  refine ⟨255195891546155012022709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5444179019651306923151125 255195891546155012022709)
                  ·
                    rfl

theorem cell22_2236465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 6].length) (baseStart_2236465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236465 prefixEnd_2236465 := by exact prefixLift 2236465
  have htrace : WordTrace (prefixWord ++ tailWord_2236465) baseStart_2236465 baseEnd_2236465 := by
    simpa [prefixWord, tailWord_2236465, baseEnd_2236465] using wordTrace_append hprefix tailTrace_2236465
  have hstable : (prefixWord ++ tailWord_2236465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236465).length < 2 ^ (prefixWord ++ tailWord_2236465).sum := by decide
  have hdescent : baseEnd_2236465 < baseStart_2236465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236480 : List Nat := [2, 1, 1, 2, 2, 4, 2, 2, 1, 5]
def baseStart_2236480 : Nat := 118140960795 + 2236480 * 2 ^ 59
def prefixEnd_2236480 : Nat := 4983230072969 + 3 ^ 40 * 2236480 * 2
def baseEnd_2236480 : Nat := 765592809445009996943081

theorem tailTrace_2236480 : CollatzResearch.WordTrace tailWord_2236480 prefixEnd_2236480 765592809445009996943081 := by
  unfold tailWord_2236480
  simp only [CollatzResearch.WordTrace]
  refine ⟨40785563468811197609845447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54380751291748263479793929 40785563468811197609845447)
  ·
    refine ⟨61178345203216796414768171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40785563468811197609845447 61178345203216796414768171)
    ·
      refine ⟨91767517804825194622152257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61178345203216796414768171 91767517804825194622152257)
      ·
        refine ⟨68825638353618895966614193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91767517804825194622152257 68825638353618895966614193)
        ·
          refine ⟨51619228765214171974960645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68825638353618895966614193 51619228765214171974960645)
          ·
            refine ⟨9678605393477657245305121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51619228765214171974960645 9678605393477657245305121)
            ·
              refine ⟨7258954045108242933978841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9678605393477657245305121 7258954045108242933978841)
              ·
                refine ⟨5444215533831182200484131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7258954045108242933978841 5444215533831182200484131)
                ·
                  refine ⟨8166323300746773300726197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5444215533831182200484131 8166323300746773300726197)
                  ·
                    refine ⟨765592809445009996943081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8166323300746773300726197 765592809445009996943081)
                    ·
                      rfl

theorem cell22_2236480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_2236480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236480 prefixEnd_2236480 := by exact prefixLift 2236480
  have htrace : WordTrace (prefixWord ++ tailWord_2236480) baseStart_2236480 baseEnd_2236480 := by
    simpa [prefixWord, tailWord_2236480, baseEnd_2236480] using wordTrace_append hprefix tailTrace_2236480
  have hstable : (prefixWord ++ tailWord_2236480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236480).length < 2 ^ (prefixWord ++ tailWord_2236480).sum := by decide
  have hdescent : baseEnd_2236480 < baseStart_2236480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236525 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_2236525 : Nat := 118140960795 + 2236525 * 2 ^ 59
def prefixEnd_2236525 : Nat := 4983230072969 + 3 ^ 40 * 2236525 * 2
def baseEnd_2236525 : Nat := 765608213864644879567943

theorem tailTrace_2236525 : CollatzResearch.WordTrace tailWord_2236525 prefixEnd_2236525 765608213864644879567943 := by
  unfold tailWord_2236525
  simp only [CollatzResearch.WordTrace]
  refine ⟨81572768222459367905079029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54381845481639578603386019 81572768222459367905079029)
  ·
    refine ⟨7647447020855565741101159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81572768222459367905079029 7647447020855565741101159)
    ·
      refine ⟨11471170531283348611651739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7647447020855565741101159 11471170531283348611651739)
      ·
        refine ⟨17206755796925022917477609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11471170531283348611651739 17206755796925022917477609)
        ·
          refine ⟨12905066847693767188108207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17206755796925022917477609 12905066847693767188108207)
          ·
            refine ⟨19357600271540650782162311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12905066847693767188108207 19357600271540650782162311)
            ·
              refine ⟨29036400407310976173243467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19357600271540650782162311 29036400407310976173243467)
              ·
                refine ⟨43554600610966464259865201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29036400407310976173243467 43554600610966464259865201)
                ·
                  refine ⟨32665950458224848194898901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43554600610966464259865201 32665950458224848194898901)
                  ·
                    refine ⟨765608213864644879567943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32665950458224848194898901 765608213864644879567943)
                    ·
                      rfl

theorem cell22_2236525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_2236525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236525 prefixEnd_2236525 := by exact prefixLift 2236525
  have htrace : WordTrace (prefixWord ++ tailWord_2236525) baseStart_2236525 baseEnd_2236525 := by
    simpa [prefixWord, tailWord_2236525, baseEnd_2236525] using wordTrace_append hprefix tailTrace_2236525
  have hstable : (prefixWord ++ tailWord_2236525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236525).length < 2 ^ (prefixWord ++ tailWord_2236525).sum := by decide
  have hdescent : baseEnd_2236525 < baseStart_2236525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236527 : List Nat := [1, 1, 2, 1, 3, 6, 2, 6]
def baseStart_2236527 : Nat := 118140960795 + 2236527 * 2 ^ 59
def prefixEnd_2236527 : Nat := 4983230072969 + 3 ^ 40 * 2236527 * 2
def baseEnd_2236527 : Nat := 85067655389501949001993

theorem tailTrace_2236527 : CollatzResearch.WordTrace tailWord_2236527 prefixEnd_2236527 85067655389501949001993 := by
  unfold tailWord_2236527
  simp only [CollatzResearch.WordTrace]
  refine ⟨81572841168452122246651835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54381894112301414831101223 81572841168452122246651835)
  ·
    refine ⟨122359261752678183369977753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81572841168452122246651835 122359261752678183369977753)
    ·
      refine ⟨91769446314508637527483315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122359261752678183369977753 91769446314508637527483315)
      ·
        refine ⟨137654169471762956291224973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91769446314508637527483315 137654169471762956291224973)
        ·
          refine ⟨51620313551911108609209365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137654169471762956291224973 51620313551911108609209365)
          ·
            refine ⟨2419702197745833216056689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 51620313551911108609209365 2419702197745833216056689)
            ·
              refine ⟨1814776648309374912042517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2419702197745833216056689 1814776648309374912042517)
              ·
                refine ⟨85067655389501949001993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1814776648309374912042517 85067655389501949001993)
                ·
                  rfl

theorem cell22_2236527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 6].length) (baseStart_2236527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236527 prefixEnd_2236527 := by exact prefixLift 2236527
  have htrace : WordTrace (prefixWord ++ tailWord_2236527) baseStart_2236527 baseEnd_2236527 := by
    simpa [prefixWord, tailWord_2236527, baseEnd_2236527] using wordTrace_append hprefix tailTrace_2236527
  have hstable : (prefixWord ++ tailWord_2236527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236527).length < 2 ^ (prefixWord ++ tailWord_2236527).sum := by decide
  have hdescent : baseEnd_2236527 < baseStart_2236527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236572 : List Nat := [2, 2, 3, 2, 1, 1, 3, 3, 5]
def baseStart_2236572 : Nat := 118140960795 + 2236572 * 2 ^ 59
def prefixEnd_2236572 : Nat := 4983230072969 + 3 ^ 40 * 2236572 * 2
def baseEnd_2236572 : Nat := 255208100975050807880933

theorem tailTrace_2236572 : CollatzResearch.WordTrace tailWord_2236572 prefixEnd_2236572 255208100975050807880933 := by
  unfold tailWord_2236572
  simp only [CollatzResearch.WordTrace]
  refine ⟨40787241226644547466019985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54382988302192729954693313 40787241226644547466019985)
  ·
    refine ⟨30590430919983410599514989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40787241226644547466019985 30590430919983410599514989)
    ·
      refine ⟨11471411594993778974818121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30590430919983410599514989 11471411594993778974818121)
      ·
        refine ⟨8603558696245334231113591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11471411594993778974818121 8603558696245334231113591)
        ·
          refine ⟨12905338044368001346670387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8603558696245334231113591 12905338044368001346670387)
          ·
            refine ⟨19358007066552002020005581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12905338044368001346670387 19358007066552002020005581)
            ·
              refine ⟨7259252649957000757502093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19358007066552002020005581 7259252649957000757502093)
              ·
                refine ⟨2722219743733875284063285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7259252649957000757502093 2722219743733875284063285)
                ·
                  refine ⟨255208100975050807880933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2722219743733875284063285 255208100975050807880933)
                  ·
                    rfl

theorem cell22_2236572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_2236572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236572 prefixEnd_2236572 := by exact prefixLift 2236572
  have htrace : WordTrace (prefixWord ++ tailWord_2236572) baseStart_2236572 baseEnd_2236572 := by
    simpa [prefixWord, tailWord_2236572, baseEnd_2236572] using wordTrace_append hprefix tailTrace_2236572
  have hstable : (prefixWord ++ tailWord_2236572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236572).length < 2 ^ (prefixWord ++ tailWord_2236572).sum := by decide
  have hdescent : baseEnd_2236572 < baseStart_2236572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236602 : List Nat := [3, 1, 1, 1, 2, 2, 2, 5, 1, 4]
def baseStart_2236602 : Nat := 118140960795 + 2236602 * 2 ^ 59
def prefixEnd_2236602 : Nat := 4983230072969 + 3 ^ 40 * 2236602 * 2
def baseEnd_2236602 : Nat := 765634572538242345392707

theorem tailTrace_2236602 : CollatzResearch.WordTrace tailWord_2236602 prefixEnd_2236602 765634572538242345392707 := by
  unfold tailWord_2236602
  simp only [CollatzResearch.WordTrace]
  refine ⟨20393894160795102513908015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54383717762120273370421373 20393894160795102513908015)
  ·
    refine ⟨30590841241192653770862023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20393894160795102513908015 30590841241192653770862023)
    ·
      refine ⟨45886261861788980656293035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30590841241192653770862023 45886261861788980656293035)
      ·
        refine ⟨68829392792683470984439553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45886261861788980656293035 68829392792683470984439553)
        ·
          refine ⟨51622044594512603238329665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68829392792683470984439553 51622044594512603238329665)
          ·
            refine ⟨38716533445884452428747249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51622044594512603238329665 38716533445884452428747249)
            ·
              refine ⟨29037400084413339321560437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38716533445884452428747249 29037400084413339321560437)
              ·
                refine ⟨2722256257913750561396291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29037400084413339321560437 2722256257913750561396291)
                ·
                  refine ⟨4083384386870625842094437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2722256257913750561396291 4083384386870625842094437)
                  ·
                    refine ⟨765634572538242345392707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4083384386870625842094437 765634572538242345392707)
                    ·
                      rfl

theorem cell22_2236602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_2236602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236602 prefixEnd_2236602 := by exact prefixLift 2236602
  have htrace : WordTrace (prefixWord ++ tailWord_2236602) baseStart_2236602 baseEnd_2236602 := by
    simpa [prefixWord, tailWord_2236602, baseEnd_2236602] using wordTrace_append hprefix tailTrace_2236602
  have hstable : (prefixWord ++ tailWord_2236602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236602).length < 2 ^ (prefixWord ++ tailWord_2236602).sum := by decide
  have hdescent : baseEnd_2236602 < baseStart_2236602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236610 : List Nat := [3, 5, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_2236610 : Nat := 118140960795 + 2236610 * 2 ^ 59
def prefixEnd_2236610 : Nat := 4983230072969 + 3 ^ 40 * 2236610 * 2
def baseEnd_2236610 : Nat := 765637311101732991192683

theorem tailTrace_2236610 : CollatzResearch.WordTrace tailWord_2236610 prefixEnd_2236610 765637311101732991192683 := by
  unfold tailWord_2236610
  simp only [CollatzResearch.WordTrace]
  refine ⟨20393967106787856855480821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54383912284767618281282189 20393967106787856855480821)
  ·
    refine ⟨1911934416261361580201327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20393967106787856855480821 1911934416261361580201327)
    ·
      refine ⟨2867901624392042370301991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1911934416261361580201327 2867901624392042370301991)
      ·
        refine ⟨4301852436588063555452987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2867901624392042370301991 4301852436588063555452987)
        ·
          refine ⟨6452778654882095333179481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4301852436588063555452987 6452778654882095333179481)
          ·
            refine ⟨4839583991161571499884611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6452778654882095333179481 4839583991161571499884611)
            ·
              refine ⟨7259375986742357249826917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4839583991161571499884611 7259375986742357249826917)
              ·
                refine ⟨1361132997514191984342547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7259375986742357249826917 1361132997514191984342547)
                ·
                  refine ⟨2041699496271287976513821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1361132997514191984342547 2041699496271287976513821)
                  ·
                    refine ⟨765637311101732991192683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2041699496271287976513821 765637311101732991192683)
                    ·
                      rfl

theorem cell22_2236610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_2236610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236610 prefixEnd_2236610 := by exact prefixLift 2236610
  have htrace : WordTrace (prefixWord ++ tailWord_2236610) baseStart_2236610 baseEnd_2236610 := by
    simpa [prefixWord, tailWord_2236610, baseEnd_2236610] using wordTrace_append hprefix tailTrace_2236610
  have hstable : (prefixWord ++ tailWord_2236610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236610).length < 2 ^ (prefixWord ++ tailWord_2236610).sum := by decide
  have hdescent : baseEnd_2236610 < baseStart_2236610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236632 : List Nat := [2, 1, 2, 2, 4, 1, 1, 3, 1, 5]
def baseStart_2236632 : Nat := 118140960795 + 2236632 * 2 ^ 59
def prefixEnd_2236632 : Nat := 4983230072969 + 3 ^ 40 * 2236632 * 2
def baseEnd_2236632 : Nat := 765644842151332267142615

theorem tailTrace_2236632 : CollatzResearch.WordTrace tailWord_2236632 prefixEnd_2236632 765644842151332267142615 := by
  unfold tailWord_2236632
  simp only [CollatzResearch.WordTrace]
  refine ⟨40788335416535862589612075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54384447222047816786149433 40788335416535862589612075)
  ·
    refine ⟨61182503124803793884418113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40788335416535862589612075 61182503124803793884418113)
    ·
      refine ⟨45886877343602845413313585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61182503124803793884418113 45886877343602845413313585)
      ·
        refine ⟨34415158007702134059985189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45886877343602845413313585 34415158007702134059985189)
        ·
          refine ⟨6452842126444150136247223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34415158007702134059985189 6452842126444150136247223)
          ·
            refine ⟨9679263189666225204370835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6452842126444150136247223 9679263189666225204370835)
            ·
              refine ⟨14518894784499337806556253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9679263189666225204370835 14518894784499337806556253)
              ·
                refine ⟨5444585544187251677458595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14518894784499337806556253 5444585544187251677458595)
                ·
                  refine ⟨8166878316280877516187893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5444585544187251677458595 8166878316280877516187893)
                  ·
                    refine ⟨765644842151332267142615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8166878316280877516187893 765644842151332267142615)
                    ·
                      rfl

theorem cell22_2236632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_2236632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236632 prefixEnd_2236632 := by exact prefixLift 2236632
  have htrace : WordTrace (prefixWord ++ tailWord_2236632) baseStart_2236632 baseEnd_2236632 := by
    simpa [prefixWord, tailWord_2236632, baseEnd_2236632] using wordTrace_append hprefix tailTrace_2236632
  have hstable : (prefixWord ++ tailWord_2236632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236632).length < 2 ^ (prefixWord ++ tailWord_2236632).sum := by decide
  have hdescent : baseEnd_2236632 < baseStart_2236632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236653 : List Nat := [1, 5, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_2236653 : Nat := 118140960795 + 2236653 * 2 ^ 59
def prefixEnd_2236653 : Nat := 4983230072969 + 3 ^ 40 * 2236653 * 2
def baseEnd_2236653 : Nat := 765652030880495212367551

theorem tailTrace_2236653 : CollatzResearch.WordTrace tailWord_2236653 prefixEnd_2236653 765652030880495212367551 := by
  unfold tailWord_2236653
  simp only [CollatzResearch.WordTrace]
  refine ⟨81577436765995645765738613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54384957843997097177159075 81577436765995645765738613)
  ·
    refine ⟨7647884696812091790537995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81577436765995645765738613 7647884696812091790537995)
    ·
      refine ⟨11471827045218137685806993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7647884696812091790537995 11471827045218137685806993)
      ·
        refine ⟨8603870283913603264355245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11471827045218137685806993 8603870283913603264355245)
        ·
          refine ⟨3226451356467601224133217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8603870283913603264355245 3226451356467601224133217)
          ·
            refine ⟨2419838517350700918099913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3226451356467601224133217 2419838517350700918099913)
            ·
              refine ⟨1814878888013025688574935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2419838517350700918099913 1814878888013025688574935)
              ·
                refine ⟨2722318332019538532862403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1814878888013025688574935 2722318332019538532862403)
                ·
                  refine ⟨4083477498029307799293605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2722318332019538532862403 4083477498029307799293605)
                  ·
                    refine ⟨765652030880495212367551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4083477498029307799293605 765652030880495212367551)
                    ·
                      rfl

theorem cell22_2236653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_2236653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236653 prefixEnd_2236653 := by exact prefixLift 2236653
  have htrace : WordTrace (prefixWord ++ tailWord_2236653) baseStart_2236653 baseEnd_2236653 := by
    simpa [prefixWord, tailWord_2236653, baseEnd_2236653] using wordTrace_append hprefix tailTrace_2236653
  have hstable : (prefixWord ++ tailWord_2236653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236653).length < 2 ^ (prefixWord ++ tailWord_2236653).sum := by decide
  have hdescent : baseEnd_2236653 < baseStart_2236653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236666 : List Nat := [3, 1, 1, 1, 1, 7, 1, 2, 2, 3]
def baseStart_2236666 : Nat := 118140960795 + 2236666 * 2 ^ 59
def prefixEnd_2236666 : Nat := 4983230072969 + 3 ^ 40 * 2236666 * 2
def baseEnd_2236666 : Nat := 765656481046167511792511

theorem tailTrace_2236666 : CollatzResearch.WordTrace tailWord_2236666 prefixEnd_2236666 765656481046167511792511 := by
  unfold tailWord_2236666
  simp only [CollatzResearch.WordTrace]
  refine ⟨20394477728737137246490463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54385273943299032657307901 20394477728737137246490463)
  ·
    refine ⟨30591716593105705869735695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20394477728737137246490463 30591716593105705869735695)
    ·
      refine ⟨45887574889658558804603543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30591716593105705869735695 45887574889658558804603543)
      ·
        refine ⟨68831362334487838206905315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45887574889658558804603543 68831362334487838206905315)
        ·
          refine ⟨103247043501731757310357973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68831362334487838206905315 103247043501731757310357973)
          ·
            refine ⟨2419852582071838061961515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 103247043501731757310357973 2419852582071838061961515)
            ·
              refine ⟨3629778873107757092942273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2419852582071838061961515 3629778873107757092942273)
              ·
                refine ⟨2722334154830817819706705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3629778873107757092942273 2722334154830817819706705)
                ·
                  refine ⟨2041750616123113364780029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2722334154830817819706705 2041750616123113364780029)
                  ·
                    refine ⟨765656481046167511792511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2041750616123113364780029 765656481046167511792511)
                    ·
                      rfl

theorem cell22_2236666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_2236666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236666 prefixEnd_2236666 := by exact prefixLift 2236666
  have htrace : WordTrace (prefixWord ++ tailWord_2236666) baseStart_2236666 baseEnd_2236666 := by
    simpa [prefixWord, tailWord_2236666, baseEnd_2236666] using wordTrace_append hprefix tailTrace_2236666
  have hstable : (prefixWord ++ tailWord_2236666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236666).length < 2 ^ (prefixWord ++ tailWord_2236666).sum := by decide
  have hdescent : baseEnd_2236666 < baseStart_2236666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236724 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 7]
def baseStart_2236724 : Nat := 118140960795 + 2236724 * 2 ^ 59
def prefixEnd_2236724 : Nat := 4983230072969 + 3 ^ 40 * 2236724 * 2
def baseEnd_2236724 : Nat := 255225445210491564614111

theorem tailTrace_2236724 : CollatzResearch.WordTrace tailWord_2236724 prefixEnd_2236724 255225445210491564614111 := by
  unfold tailWord_2236724
  simp only [CollatzResearch.WordTrace]
  refine ⟨40790013174369212445786613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54386684232492283261048817 40790013174369212445786613)
  ·
    refine ⟨3824063735097113666792495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40790013174369212445786613 3824063735097113666792495)
    ·
      refine ⟨5736095602645670500188743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3824063735097113666792495 5736095602645670500188743)
      ·
        refine ⟨8604143403968505750283115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5736095602645670500188743 8604143403968505750283115)
        ·
          refine ⟨12906215105952758625424673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8604143403968505750283115 12906215105952758625424673)
          ·
            refine ⟨9679661329464568969068505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12906215105952758625424673 9679661329464568969068505)
            ·
              refine ⟨7259745997098426726801379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9679661329464568969068505 7259745997098426726801379)
              ·
                refine ⟨10889618995647640090202069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7259745997098426726801379 10889618995647640090202069)
                ·
                  refine ⟨255225445210491564614111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10889618995647640090202069 255225445210491564614111)
                  ·
                    rfl

theorem cell22_2236724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_2236724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236724 prefixEnd_2236724 := by exact prefixLift 2236724
  have htrace : WordTrace (prefixWord ++ tailWord_2236724) baseStart_2236724 baseEnd_2236724 := by
    simpa [prefixWord, tailWord_2236724, baseEnd_2236724] using wordTrace_append hprefix tailTrace_2236724
  have hstable : (prefixWord ++ tailWord_2236724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236724).length < 2 ^ (prefixWord ++ tailWord_2236724).sum := by decide
  have hdescent : baseEnd_2236724 < baseStart_2236724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236767 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 3, 5]
def baseStart_2236767 : Nat := 118140960795 + 2236767 * 2 ^ 59
def prefixEnd_2236767 : Nat := 4983230072969 + 3 ^ 40 * 2236767 * 2
def baseEnd_2236767 : Nat := 765691055410236915017201

theorem tailTrace_2236767 : CollatzResearch.WordTrace tailWord_2236767 prefixEnd_2236767 765691055410236915017201 := by
  unfold tailWord_2236767
  simp only [CollatzResearch.WordTrace]
  refine ⟨81581594687582643235388555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54387729791721762156925703 81581594687582643235388555)
  ·
    refine ⟨122372392031373964853082833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81581594687582643235388555 122372392031373964853082833)
    ·
      refine ⟨91779294023530473639812125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122372392031373964853082833 91779294023530473639812125)
      ·
        refine ⟨34417235258823927614929547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91779294023530473639812125 34417235258823927614929547)
        ·
          refine ⟨51625852888235891422394321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34417235258823927614929547 51625852888235891422394321)
          ·
            refine ⟨38719389666176918566795741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51625852888235891422394321 38719389666176918566795741)
            ·
              refine ⟨14519771124816344462548403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38719389666176918566795741 14519771124816344462548403)
              ·
                refine ⟨21779656687224516693822605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14519771124816344462548403 21779656687224516693822605)
                ·
                  refine ⟨8167371257709193760183477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21779656687224516693822605 8167371257709193760183477)
                  ·
                    refine ⟨765691055410236915017201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8167371257709193760183477 765691055410236915017201)
                    ·
                      rfl

theorem cell22_2236767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_2236767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236767 prefixEnd_2236767 := by exact prefixLift 2236767
  have htrace : WordTrace (prefixWord ++ tailWord_2236767) baseStart_2236767 baseEnd_2236767 := by
    simpa [prefixWord, tailWord_2236767, baseEnd_2236767] using wordTrace_append hprefix tailTrace_2236767
  have hstable : (prefixWord ++ tailWord_2236767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236767).length < 2 ^ (prefixWord ++ tailWord_2236767).sum := by decide
  have hdescent : baseEnd_2236767 < baseStart_2236767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236771 : List Nat := [1, 1, 1, 5, 2, 1, 5, 1, 1, 4]
def baseStart_2236771 : Nat := 118140960795 + 2236771 * 2 ^ 59
def prefixEnd_2236771 : Nat := 4983230072969 + 3 ^ 40 * 2236771 * 2
def baseEnd_2236771 : Nat := 765692424691982237917189

theorem tailTrace_2236771 : CollatzResearch.WordTrace tailWord_2236771 prefixEnd_2236771 765692424691982237917189 := by
  unfold tailWord_2236771
  simp only [CollatzResearch.WordTrace]
  refine ⟨81581740579568151918534167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54387827053045434612356111 81581740579568151918534167)
  ·
    refine ⟨122372610869352227877801251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81581740579568151918534167 122372610869352227877801251)
    ·
      refine ⟨183558916304028341816701877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122372610869352227877801251 183558916304028341816701877)
      ·
        refine ⟨17208648403502657045315801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 183558916304028341816701877 17208648403502657045315801)
        ·
          refine ⟨12906486302626992783986851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17208648403502657045315801 12906486302626992783986851)
          ·
            refine ⟨19359729453940489175980277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12906486302626992783986851 19359729453940489175980277)
            ·
              refine ⟨1814974636306920860248151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19359729453940489175980277 1814974636306920860248151)
              ·
                refine ⟨2722461954460381290372227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1814974636306920860248151 2722461954460381290372227)
                ·
                  refine ⟨4083692931690571935558341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2722461954460381290372227 4083692931690571935558341)
                  ·
                    refine ⟨765692424691982237917189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4083692931690571935558341 765692424691982237917189)
                    ·
                      rfl

theorem cell22_2236771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 1, 4].length) (baseStart_2236771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236771 prefixEnd_2236771 := by exact prefixLift 2236771
  have htrace : WordTrace (prefixWord ++ tailWord_2236771) baseStart_2236771 baseEnd_2236771 := by
    simpa [prefixWord, tailWord_2236771, baseEnd_2236771] using wordTrace_append hprefix tailTrace_2236771
  have hstable : (prefixWord ++ tailWord_2236771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236771).length < 2 ^ (prefixWord ++ tailWord_2236771).sum := by decide
  have hdescent : baseEnd_2236771 < baseStart_2236771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236786 : List Nat := [3, 2, 1, 2, 1, 4, 1, 4, 4]
def baseStart_2236786 : Nat := 118140960795 + 2236786 * 2 ^ 59
def prefixEnd_2236786 : Nat := 4983230072969 + 3 ^ 40 * 2236786 * 2
def baseEnd_2236786 : Nat := 255232519832842399597381

theorem tailTrace_2236786 : CollatzResearch.WordTrace tailWord_2236786 prefixEnd_2236786 255232519832842399597381 := by
  unfold tailWord_2236786
  simp only [CollatzResearch.WordTrace]
  refine ⟨20395571918628452370082553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54388191783009206320220141 20395571918628452370082553)
  ·
    refine ⟨15296678938971339277561915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20395571918628452370082553 15296678938971339277561915)
    ·
      refine ⟨22945018408457008916342873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15296678938971339277561915 22945018408457008916342873)
      ·
        refine ⟨17208763806342756687257155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22945018408457008916342873 17208763806342756687257155)
        ·
          refine ⟨25813145709514135030885733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17208763806342756687257155 25813145709514135030885733)
          ·
            refine ⟨4839964820533900318291075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25813145709514135030885733 4839964820533900318291075)
            ·
              refine ⟨7259947230800850477436613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4839964820533900318291075 7259947230800850477436613)
              ·
                refine ⟨1361240105775159464519365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7259947230800850477436613 1361240105775159464519365)
                ·
                  refine ⟨255232519832842399597381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1361240105775159464519365 255232519832842399597381)
                  ·
                    rfl

theorem cell22_2236786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_2236786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236786 prefixEnd_2236786 := by exact prefixLift 2236786
  have htrace : WordTrace (prefixWord ++ tailWord_2236786) baseStart_2236786 baseEnd_2236786 := by
    simpa [prefixWord, tailWord_2236786, baseEnd_2236786] using wordTrace_append hprefix tailTrace_2236786
  have hstable : (prefixWord ++ tailWord_2236786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236786).length < 2 ^ (prefixWord ++ tailWord_2236786).sum := by decide
  have hdescent : baseEnd_2236786 < baseStart_2236786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236801 : List Nat := [1, 2, 4, 3, 1, 2, 2, 1, 1, 5]
def baseStart_2236801 : Nat := 118140960795 + 2236801 * 2 ^ 59
def prefixEnd_2236801 : Nat := 4983230072969 + 3 ^ 40 * 2236801 * 2
def baseEnd_2236801 : Nat := 765702694305072159667097

theorem tailTrace_2236801 : CollatzResearch.WordTrace tailWord_2236801 prefixEnd_2236801 765702694305072159667097 := by
  unfold tailWord_2236801
  simp only [CollatzResearch.WordTrace]
  refine ⟨81582834769459467042126257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54388556512972978028084171 81582834769459467042126257)
  ·
    refine ⟨61187126077094600281594693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81582834769459467042126257 61187126077094600281594693)
    ·
      refine ⟨11472586139455237552799005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61187126077094600281594693 11472586139455237552799005)
      ·
        refine ⟨4302219802295714082299627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11472586139455237552799005 4302219802295714082299627)
        ·
          refine ⟨6453329703443571123449441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4302219802295714082299627 6453329703443571123449441)
          ·
            refine ⟨4839997277582678342587081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6453329703443571123449441 4839997277582678342587081)
            ·
              refine ⟨3629997958187008756940311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4839997277582678342587081 3629997958187008756940311)
              ·
                refine ⟨5444996937280513135410467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3629997958187008756940311 5444996937280513135410467)
                ·
                  refine ⟨8167495405920769703115701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5444996937280513135410467 8167495405920769703115701)
                  ·
                    refine ⟨765702694305072159667097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8167495405920769703115701 765702694305072159667097)
                    ·
                      rfl

theorem cell22_2236801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_2236801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236801 prefixEnd_2236801 := by exact prefixLift 2236801
  have htrace : WordTrace (prefixWord ++ tailWord_2236801) baseStart_2236801 baseEnd_2236801 := by
    simpa [prefixWord, tailWord_2236801, baseEnd_2236801] using wordTrace_append hprefix tailTrace_2236801
  have hstable : (prefixWord ++ tailWord_2236801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236801).length < 2 ^ (prefixWord ++ tailWord_2236801).sum := by decide
  have hdescent : baseEnd_2236801 < baseStart_2236801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236822 : List Nat := [5, 3, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2236822 : Nat := 118140960795 + 2236822 * 2 ^ 59
def prefixEnd_2236822 : Nat := 4983230072969 + 3 ^ 40 * 2236822 * 2
def baseEnd_2236822 : Nat := 765709883034235104892033

theorem tailTrace_2236822 : CollatzResearch.WordTrace tailWord_2236822 prefixEnd_2236822 765709883034235104892033 := by
  unfold tailWord_2236822
  simp only [CollatzResearch.WordTrace]
  refine ⟨5098975043898961726790045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54389067134922258419093813 5098975043898961726790045)
  ·
    refine ⟨1912115641462110647546267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5098975043898961726790045 1912115641462110647546267)
    ·
      refine ⟨2868173462193165971319401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1912115641462110647546267 2868173462193165971319401)
      ·
        refine ⟨2151130096644874478489551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2868173462193165971319401 2151130096644874478489551)
        ·
          refine ⟨3226695144967311717734327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2151130096644874478489551 3226695144967311717734327)
          ·
            refine ⟨4840042717450967576601491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3226695144967311717734327 4840042717450967576601491)
            ·
              refine ⟨7260064076176451364902237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4840042717450967576601491 7260064076176451364902237)
              ·
                refine ⟨2722524028566169261838339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7260064076176451364902237 2722524028566169261838339)
                ·
                  refine ⟨4083786042849253892757509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2722524028566169261838339 4083786042849253892757509)
                  ·
                    refine ⟨765709883034235104892033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4083786042849253892757509 765709883034235104892033)
                    ·
                      rfl

theorem cell22_2236822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2236822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236822 prefixEnd_2236822 := by exact prefixLift 2236822
  have htrace : WordTrace (prefixWord ++ tailWord_2236822) baseStart_2236822 baseEnd_2236822 := by
    simpa [prefixWord, tailWord_2236822, baseEnd_2236822] using wordTrace_append hprefix tailTrace_2236822
  have hstable : (prefixWord ++ tailWord_2236822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236822).length < 2 ^ (prefixWord ++ tailWord_2236822).sum := by decide
  have hdescent : baseEnd_2236822 < baseStart_2236822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236852 : List Nat := [2, 5, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_2236852 : Nat := 118140960795 + 2236852 * 2 ^ 59
def prefixEnd_2236852 : Nat := 4983230072969 + 3 ^ 40 * 2236852 * 2
def baseEnd_2236852 : Nat := 765720152647325026641941

theorem tailTrace_2236852 : CollatzResearch.WordTrace tailWord_2236852 prefixEnd_2236852 765720152647325026641941 := by
  unfold tailWord_2236852
  simp only [CollatzResearch.WordTrace]
  refine ⟨40792347446137351376116405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54389796594849801834821873 40792347446137351376116405)
  ·
    refine ⟨3824282573075376691510913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40792347446137351376116405 3824282573075376691510913)
    ·
      refine ⟨2868211929806532518633185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3824282573075376691510913 2868211929806532518633185)
      ·
        refine ⟨2151158947354899388974889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2868211929806532518633185 2151158947354899388974889)
        ·
          refine ⟨1613369210516174541731167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2151158947354899388974889 1613369210516174541731167)
          ·
            refine ⟨2420053815774261812596751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1613369210516174541731167 2420053815774261812596751)
            ·
              refine ⟨3630080723661392718895127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2420053815774261812596751 3630080723661392718895127)
              ·
                refine ⟨5445121085492089078342691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3630080723661392718895127 5445121085492089078342691)
                ·
                  refine ⟨8167681628238133617514037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5445121085492089078342691 8167681628238133617514037)
                  ·
                    refine ⟨765720152647325026641941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8167681628238133617514037 765720152647325026641941)
                    ·
                      rfl

theorem cell22_2236852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_2236852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236852 prefixEnd_2236852 := by exact prefixLift 2236852
  have htrace : WordTrace (prefixWord ++ tailWord_2236852) baseStart_2236852 baseEnd_2236852 := by
    simpa [prefixWord, tailWord_2236852, baseEnd_2236852] using wordTrace_append hprefix tailTrace_2236852
  have hstable : (prefixWord ++ tailWord_2236852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236852).length < 2 ^ (prefixWord ++ tailWord_2236852).sum := by decide
  have hdescent : baseEnd_2236852 < baseStart_2236852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236979 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 2, 6]
def baseStart_2236979 : Nat := 118140960795 + 2236979 * 2 ^ 59
def prefixEnd_2236979 : Nat := 4983230072969 + 3 ^ 40 * 2236979 * 2
def baseEnd_2236979 : Nat := 765763627342739028716551

theorem tailTrace_2236979 : CollatzResearch.WordTrace tailWord_2236979 prefixEnd_2236979 765763627342739028716551 := by
  unfold tailWord_2236979
  simp only [CollatzResearch.WordTrace]
  refine ⟨81589326962814603442105991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54392884641876402294737327 81589326962814603442105991)
  ·
    refine ⟨122383990444221905163158987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81589326962814603442105991 122383990444221905163158987)
    ·
      refine ⟨183575985666332857744738481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122383990444221905163158987 183575985666332857744738481)
      ·
        refine ⟨137681989249749643308553861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183575985666332857744738481 137681989249749643308553861)
        ·
          refine ⟨25815372984328058120353849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137681989249749643308553861 25815372984328058120353849)
          ·
            refine ⟨19361529738246043590265387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25815372984328058120353849 19361529738246043590265387)
            ·
              refine ⟨29042294607369065385398081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19361529738246043590265387 29042294607369065385398081)
              ·
                refine ⟨21781720955526799039048561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29042294607369065385398081 21781720955526799039048561)
                ·
                  refine ⟨16336290716645099279286421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21781720955526799039048561 16336290716645099279286421)
                  ·
                    refine ⟨765763627342739028716551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16336290716645099279286421 765763627342739028716551)
                    ·
                      rfl

theorem cell22_2236979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 6].length) (baseStart_2236979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2236979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2236979 prefixEnd_2236979 := by exact prefixLift 2236979
  have htrace : WordTrace (prefixWord ++ tailWord_2236979) baseStart_2236979 baseEnd_2236979 := by
    simpa [prefixWord, tailWord_2236979, baseEnd_2236979] using wordTrace_append hprefix tailTrace_2236979
  have hstable : (prefixWord ++ tailWord_2236979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236979).length < 2 ^ (prefixWord ++ tailWord_2236979).sum := by decide
  have hdescent : baseEnd_2236979 < baseStart_2236979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237028 : List Nat := [2, 3, 1, 1, 2, 2, 5, 1, 5]
def baseStart_2237028 : Nat := 118140960795 + 2237028 * 2 ^ 59
def prefixEnd_2237028 : Nat := 4983230072969 + 3 ^ 40 * 2237028 * 2
def baseEnd_2237028 : Nat := 255260133681373078080467

theorem tailTrace_2237028 : CollatzResearch.WordTrace tailWord_2237028 prefixEnd_2237028 255260133681373078080467 := by
  unfold tailWord_2237028
  simp only [CollatzResearch.WordTrace]
  refine ⟨40795557069818542405319869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54394076093091389873759825 40795557069818542405319869)
  ·
    refine ⟨15298333901181953401994951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40795557069818542405319869 15298333901181953401994951)
    ·
      refine ⟨22947500851772930102992427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15298333901181953401994951 22947500851772930102992427)
      ·
        refine ⟨34421251277659395154488641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22947500851772930102992427 34421251277659395154488641)
        ·
          refine ⟨25815938458244546365866481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34421251277659395154488641 25815938458244546365866481)
          ·
            refine ⟨19361953843683409774399861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25815938458244546365866481 19361953843683409774399861)
            ·
              refine ⟨1815183172845319666349987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19361953843683409774399861 1815183172845319666349987)
              ·
                refine ⟨2722774759267979499524981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1815183172845319666349987 2722774759267979499524981)
                ·
                  refine ⟨255260133681373078080467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2722774759267979499524981 255260133681373078080467)
                  ·
                    rfl

theorem cell22_2237028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_2237028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237028 prefixEnd_2237028 := by exact prefixLift 2237028
  have htrace : WordTrace (prefixWord ++ tailWord_2237028) baseStart_2237028 baseEnd_2237028 := by
    simpa [prefixWord, tailWord_2237028, baseEnd_2237028] using wordTrace_append hprefix tailTrace_2237028
  have hstable : (prefixWord ++ tailWord_2237028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237028).length < 2 ^ (prefixWord ++ tailWord_2237028).sum := by decide
  have hdescent : baseEnd_2237028 < baseStart_2237028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237103 : List Nat := [1, 1, 2, 1, 2, 6, 2, 1, 2, 4]
def baseStart_2237103 : Nat := 118140960795 + 2237103 * 2 ^ 59
def prefixEnd_2237103 : Nat := 4983230072969 + 3 ^ 40 * 2237103 * 2
def baseEnd_2237103 : Nat := 765806075076844038616171

theorem tailTrace_2237103 : CollatzResearch.WordTrace tailWord_2237103 prefixEnd_2237103 765806075076844038616171 := by
  unfold tailWord_2237103
  simp only [CollatzResearch.WordTrace]
  refine ⟨81593849614365372619619963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54395899742910248413079975 81593849614365372619619963)
  ·
    refine ⟨122390774421548058929429945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81593849614365372619619963 122390774421548058929429945)
    ·
      refine ⟨91793080816161044197072459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122390774421548058929429945 91793080816161044197072459)
      ·
        refine ⟨137689621224241566295608689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91793080816161044197072459 137689621224241566295608689)
        ·
          refine ⟨103267215918181174721706517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137689621224241566295608689 103267215918181174721706517)
          ·
            refine ⟨4840650746164742565079993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103267215918181174721706517 4840650746164742565079993)
            ·
              refine ⟨3630488059623556923809995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4840650746164742565079993 3630488059623556923809995)
              ·
                refine ⟨5445732089435335385714993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3630488059623556923809995 5445732089435335385714993)
                ·
                  refine ⟨4084299067076501539286245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5445732089435335385714993 4084299067076501539286245)
                  ·
                    refine ⟨765806075076844038616171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4084299067076501539286245 765806075076844038616171)
                    ·
                      rfl

theorem cell22_2237103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 4].length) (baseStart_2237103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237103 prefixEnd_2237103 := by exact prefixLift 2237103
  have htrace : WordTrace (prefixWord ++ tailWord_2237103) baseStart_2237103 baseEnd_2237103 := by
    simpa [prefixWord, tailWord_2237103, baseEnd_2237103] using wordTrace_append hprefix tailTrace_2237103
  have hstable : (prefixWord ++ tailWord_2237103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237103).length < 2 ^ (prefixWord ++ tailWord_2237103).sum := by decide
  have hdescent : baseEnd_2237103 < baseStart_2237103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237105 : List Nat := [1, 2, 2, 6, 1, 1, 1, 2, 1, 5]
def baseStart_2237105 : Nat := 118140960795 + 2237105 * 2 ^ 59
def prefixEnd_2237105 : Nat := 4983230072969 + 3 ^ 40 * 2237105 * 2
def baseEnd_2237105 : Nat := 765806759717716700066165

theorem tailTrace_2237105 : CollatzResearch.WordTrace tailWord_2237105 prefixEnd_2237105 765806759717716700066165 := by
  unfold tailWord_2237105
  simp only [CollatzResearch.WordTrace]
  refine ⟨81593922560358126961192769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54395948373572084640795179 81593922560358126961192769)
  ·
    refine ⟨61195441920268595220894577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81593922560358126961192769 61195441920268595220894577)
    ·
      refine ⟨45896581440201446415670933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61195441920268595220894577 45896581440201446415670933)
      ·
        refine ⟨2151402255009442800734575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45896581440201446415670933 2151402255009442800734575)
        ·
          refine ⟨3227103382514164201101863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2151402255009442800734575 3227103382514164201101863)
          ·
            refine ⟨4840655073771246301652795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3227103382514164201101863 4840655073771246301652795)
            ·
              refine ⟨7260982610656869452479193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4840655073771246301652795 7260982610656869452479193)
              ·
                refine ⟨5445736957992652089359395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7260982610656869452479193 5445736957992652089359395)
                ·
                  refine ⟨8168605436988978134039093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5445736957992652089359395 8168605436988978134039093)
                  ·
                    refine ⟨765806759717716700066165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8168605436988978134039093 765806759717716700066165)
                    ·
                      rfl

theorem cell22_2237105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_2237105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237105 prefixEnd_2237105 := by exact prefixLift 2237105
  have htrace : WordTrace (prefixWord ++ tailWord_2237105) baseStart_2237105 baseEnd_2237105 := by
    simpa [prefixWord, tailWord_2237105, baseEnd_2237105] using wordTrace_append hprefix tailTrace_2237105
  have hstable : (prefixWord ++ tailWord_2237105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237105).length < 2 ^ (prefixWord ++ tailWord_2237105).sum := by decide
  have hdescent : baseEnd_2237105 < baseStart_2237105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237167 : List Nat := [1, 1, 2, 1, 5, 3, 2, 3, 1, 3]
def baseStart_2237167 : Nat := 118140960795 + 2237167 * 2 ^ 59
def prefixEnd_2237167 : Nat := 4983230072969 + 3 ^ 40 * 2237167 * 2
def baseEnd_2237167 : Nat := 765827983584769205015975

theorem tailTrace_2237167 : CollatzResearch.WordTrace tailWord_2237167 prefixEnd_2237167 765827983584769205015975 := by
  unfold tailWord_2237167
  simp only [CollatzResearch.WordTrace]
  refine ⟨81596183886133511549949755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54397455924089007699966503 81596183886133511549949755)
  ·
    refine ⟨122394275829200267324924633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81596183886133511549949755 122394275829200267324924633)
    ·
      refine ⟨91795706871900200493693475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122394275829200267324924633 91795706871900200493693475)
      ·
        refine ⟨137693560307850300740540213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91795706871900200493693475 137693560307850300740540213)
        ·
          refine ⟨12908771278860965694425645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 137693560307850300740540213 12908771278860965694425645)
          ·
            refine ⟨4840789229572862135409617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12908771278860965694425645 4840789229572862135409617)
            ·
              refine ⟨3630591922179646601557213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4840789229572862135409617 3630591922179646601557213)
              ·
                refine ⟨1361471970817367475583955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3630591922179646601557213 1361471970817367475583955)
                ·
                  refine ⟨2042207956226051213375933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1361471970817367475583955 2042207956226051213375933)
                  ·
                    refine ⟨765827983584769205015975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2042207956226051213375933 765827983584769205015975)
                    ·
                      rfl

theorem cell22_2237167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 1, 3].length) (baseStart_2237167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237167 prefixEnd_2237167 := by exact prefixLift 2237167
  have htrace : WordTrace (prefixWord ++ tailWord_2237167) baseStart_2237167 baseEnd_2237167 := by
    simpa [prefixWord, tailWord_2237167, baseEnd_2237167] using wordTrace_append hprefix tailTrace_2237167
  have hstable : (prefixWord ++ tailWord_2237167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237167).length < 2 ^ (prefixWord ++ tailWord_2237167).sum := by decide
  have hdescent : baseEnd_2237167 < baseStart_2237167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237173 : List Nat := [1, 3, 6, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2237173 : Nat := 118140960795 + 2237173 * 2 ^ 59
def prefixEnd_2237173 : Nat := 4983230072969 + 3 ^ 40 * 2237173 * 2
def baseEnd_2237173 : Nat := 765830037507387189365957

theorem tailTrace_2237173 : CollatzResearch.WordTrace tailWord_2237173 prefixEnd_2237173 765830037507387189365957 := by
  unfold tailWord_2237173
  simp only [CollatzResearch.WordTrace]
  refine ⟨81596402724111774574668173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54397601816074516383112115 81596402724111774574668173)
  ·
    refine ⟨30598651021541915465500565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81596402724111774574668173 30598651021541915465500565)
    ·
      refine ⟨1434311766634777287445339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30598651021541915465500565 1434311766634777287445339)
      ·
        refine ⟨2151467649952165931168009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1434311766634777287445339 2151467649952165931168009)
        ·
          refine ⟨1613600737464124448376007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2151467649952165931168009 1613600737464124448376007)
          ·
            refine ⟨2420401106196186672564011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1613600737464124448376007 2420401106196186672564011)
            ·
              refine ⟨3630601659294280008846017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2420401106196186672564011 3630601659294280008846017)
              ·
                refine ⟨2722951244470710006634513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3630601659294280008846017 2722951244470710006634513)
                ·
                  refine ⟨2042213433353032504975885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2722951244470710006634513 2042213433353032504975885)
                  ·
                    refine ⟨765830037507387189365957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2042213433353032504975885 765830037507387189365957)
                    ·
                      rfl

theorem cell22_2237173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2237173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237173 prefixEnd_2237173 := by exact prefixLift 2237173
  have htrace : WordTrace (prefixWord ++ tailWord_2237173) baseStart_2237173 baseEnd_2237173 := by
    simpa [prefixWord, tailWord_2237173, baseEnd_2237173] using wordTrace_append hprefix tailTrace_2237173
  have hstable : (prefixWord ++ tailWord_2237173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237173).length < 2 ^ (prefixWord ++ tailWord_2237173).sum := by decide
  have hdescent : baseEnd_2237173 < baseStart_2237173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237180 : List Nat := [2, 2, 2, 1, 3, 4, 1, 2, 5]
def baseStart_2237180 : Nat := 118140960795 + 2237180 * 2 ^ 59
def prefixEnd_2237180 : Nat := 4983230072969 + 3 ^ 40 * 2237180 * 2
def baseEnd_2237180 : Nat := 255277477916813834813645

theorem tailTrace_2237180 : CollatzResearch.WordTrace tailWord_2237180 prefixEnd_2237180 255277477916813834813645 := by
  unfold tailWord_2237180
  simp only [CollatzResearch.WordTrace]
  refine ⟨40798329017543207385086497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54397772023390943180115329 40798329017543207385086497)
  ·
    refine ⟨30598746763157405538814873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40798329017543207385086497 30598746763157405538814873)
    ·
      refine ⟨22949060072368054154111155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30598746763157405538814873 22949060072368054154111155)
      ·
        refine ⟨34423590108552081231166733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22949060072368054154111155 34423590108552081231166733)
        ·
          refine ⟨12908846290707030461687525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34423590108552081231166733 12908846290707030461687525)
          ·
            refine ⟨2420408679507568211566411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12908846290707030461687525 2420408679507568211566411)
            ·
              refine ⟨3630613019261352317349617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2420408679507568211566411 3630613019261352317349617)
              ·
                refine ⟨2722959764446014238012213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3630613019261352317349617 2722959764446014238012213)
                ·
                  refine ⟨255277477916813834813645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2722959764446014238012213 255277477916813834813645)
                  ·
                    rfl

theorem cell22_2237180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_2237180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237180 prefixEnd_2237180 := by exact prefixLift 2237180
  have htrace : WordTrace (prefixWord ++ tailWord_2237180) baseStart_2237180 baseEnd_2237180 := by
    simpa [prefixWord, tailWord_2237180, baseEnd_2237180] using wordTrace_append hprefix tailTrace_2237180
  have hstable : (prefixWord ++ tailWord_2237180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237180).length < 2 ^ (prefixWord ++ tailWord_2237180).sum := by decide
  have hdescent : baseEnd_2237180 < baseStart_2237180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237210 : List Nat := [3, 1, 1, 3, 2, 1, 4, 2, 1, 4]
def baseStart_2237210 : Nat := 118140960795 + 2237210 * 2 ^ 59
def prefixEnd_2237210 : Nat := 4983230072969 + 3 ^ 40 * 2237210 * 2
def baseEnd_2237210 : Nat := 765842703363531426190843

theorem tailTrace_2237210 : CollatzResearch.WordTrace tailWord_2237210 prefixEnd_2237210 765842703363531426190843 := by
  unfold tailWord_2237210
  simp only [CollatzResearch.WordTrace]
  refine ⟨20399438056244432473441271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54398501483318486595843389 20399438056244432473441271)
  ·
    refine ⟨30599157084366648710161907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20399438056244432473441271 30599157084366648710161907)
    ·
      refine ⟨45898735626549973065242861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30599157084366648710161907 45898735626549973065242861)
      ·
        refine ⟨17212025859956239899466073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45898735626549973065242861 17212025859956239899466073)
        ·
          refine ⟨12909019394967179924599555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17212025859956239899466073 12909019394967179924599555)
          ·
            refine ⟨19363529092450769886899333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12909019394967179924599555 19363529092450769886899333)
            ·
              refine ⟨3630661704834519353793625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19363529092450769886899333 3630661704834519353793625)
              ·
                refine ⟨2722996278625889515345219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3630661704834519353793625 2722996278625889515345219)
                ·
                  refine ⟨4084494417938834273017829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2722996278625889515345219 4084494417938834273017829)
                  ·
                    refine ⟨765842703363531426190843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4084494417938834273017829 765842703363531426190843)
                    ·
                      rfl

theorem cell22_2237210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_2237210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237210 prefixEnd_2237210 := by exact prefixLift 2237210
  have htrace : WordTrace (prefixWord ++ tailWord_2237210) baseStart_2237210 baseEnd_2237210 := by
    simpa [prefixWord, tailWord_2237210, baseEnd_2237210] using wordTrace_append hprefix tailTrace_2237210
  have hstable : (prefixWord ++ tailWord_2237210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237210).length < 2 ^ (prefixWord ++ tailWord_2237210).sum := by decide
  have hdescent : baseEnd_2237210 < baseStart_2237210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237240 : List Nat := [2, 1, 2, 1, 3, 2, 2, 4, 2, 3]
def baseStart_2237240 : Nat := 118140960795 + 2237240 * 2 ^ 59
def prefixEnd_2237240 : Nat := 4983230072969 + 3 ^ 40 * 2237240 * 2
def baseEnd_2237240 : Nat := 765852972976621347940751

theorem tailTrace_2237240 : CollatzResearch.WordTrace tailWord_2237240 prefixEnd_2237240 765852972976621347940751 := by
  unfold tailWord_2237240
  simp only [CollatzResearch.WordTrace]
  refine ⟨40799423207434522508678587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54399230943246030011571449 40799423207434522508678587)
  ·
    refine ⟨61199134811151783763017881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40799423207434522508678587 61199134811151783763017881)
    ·
      refine ⟨45899351108363837822263411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61199134811151783763017881 45899351108363837822263411)
      ·
        refine ⟨68849026662545756733395117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45899351108363837822263411 68849026662545756733395117)
        ·
          refine ⟨25818384998454658775023169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68849026662545756733395117 25818384998454658775023169)
          ·
            refine ⟨19363788748840994081267377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25818384998454658775023169 19363788748840994081267377)
            ·
              refine ⟨14522841561630745560950533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19363788748840994081267377 14522841561630745560950533)
              ·
                refine ⟨2723032792805764792678225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14522841561630745560950533 2723032792805764792678225)
                ·
                  refine ⟨2042274594604323594508669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2723032792805764792678225 2042274594604323594508669)
                  ·
                    refine ⟨765852972976621347940751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2042274594604323594508669 765852972976621347940751)
                    ·
                      rfl

theorem cell22_2237240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_2237240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237240 prefixEnd_2237240 := by exact prefixLift 2237240
  have htrace : WordTrace (prefixWord ++ tailWord_2237240) baseStart_2237240 baseEnd_2237240 := by
    simpa [prefixWord, tailWord_2237240, baseEnd_2237240] using wordTrace_append hprefix tailTrace_2237240
  have hstable : (prefixWord ++ tailWord_2237240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237240).length < 2 ^ (prefixWord ++ tailWord_2237240).sum := by decide
  have hdescent : baseEnd_2237240 < baseStart_2237240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237242 : List Nat := [3, 1, 1, 1, 7, 1, 1, 1, 6]
def baseStart_2237242 : Nat := 118140960795 + 2237242 * 2 ^ 59
def prefixEnd_2237242 : Nat := 4983230072969 + 3 ^ 40 * 2237242 * 2
def baseEnd_2237242 : Nat := 255284552539164669796915

theorem tailTrace_2237242 : CollatzResearch.WordTrace tailWord_2237242 prefixEnd_2237242 255284552539164669796915 := by
  unfold tailWord_2237242
  simp only [CollatzResearch.WordTrace]
  refine ⟨20399729840215449839732495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54399279573907866239286653 20399729840215449839732495)
  ·
    refine ⟨30599594760323174759598743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20399729840215449839732495 30599594760323174759598743)
    ·
      refine ⟨45899392140484762139398115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30599594760323174759598743 45899392140484762139398115)
      ·
        refine ⟨68849088210727143209097173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45899392140484762139398115 68849088210727143209097173)
        ·
          refine ⟨1613650504938917418963215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 68849088210727143209097173 1613650504938917418963215)
          ·
            refine ⟨2420475757408376128444823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1613650504938917418963215 2420475757408376128444823)
            ·
              refine ⟨3630713636112564192667235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2420475757408376128444823 3630713636112564192667235)
              ·
                refine ⟨5446070454168846289000853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3630713636112564192667235 5446070454168846289000853)
                ·
                  refine ⟨255284552539164669796915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5446070454168846289000853 255284552539164669796915)
                  ·
                    rfl

theorem cell22_2237242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_2237242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237242 prefixEnd_2237242 := by exact prefixLift 2237242
  have htrace : WordTrace (prefixWord ++ tailWord_2237242) baseStart_2237242 baseEnd_2237242 := by
    simpa [prefixWord, tailWord_2237242, baseEnd_2237242] using wordTrace_append hprefix tailTrace_2237242
  have hstable : (prefixWord ++ tailWord_2237242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237242).length < 2 ^ (prefixWord ++ tailWord_2237242).sum := by decide
  have hdescent : baseEnd_2237242 < baseStart_2237242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237257 : List Nat := [1, 2, 1, 1, 2, 5, 4, 1, 2, 3]
def baseStart_2237257 : Nat := 118140960795 + 2237257 * 2 ^ 59
def prefixEnd_2237257 : Nat := 4983230072969 + 3 ^ 40 * 2237257 * 2
def baseEnd_2237257 : Nat := 765858792424038970265699

theorem tailTrace_2237257 : CollatzResearch.WordTrace tailWord_2237257 prefixEnd_2237257 765858792424038970265699 := by
  unfold tailWord_2237257
  simp only [CollatzResearch.WordTrace]
  refine ⟨81599466455807456920726025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54399644303871637947150683 81599466455807456920726025)
  ·
    refine ⟨61199599841855592690544519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81599466455807456920726025 61199599841855592690544519)
    ·
      refine ⟨91799399762783389035816779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61199599841855592690544519 91799399762783389035816779)
      ·
        refine ⟨137699099644175083553725169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91799399762783389035816779 137699099644175083553725169)
        ·
          refine ⟨103274324733131312665293877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137699099644175083553725169 103274324733131312665293877)
          ·
            refine ⟨9681967943731060562371301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103274324733131312665293877 9681967943731060562371301)
            ·
              refine ⟨1815368989449573855444619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9681967943731060562371301 1815368989449573855444619)
              ·
                refine ⟨2723053484174360783166929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1815368989449573855444619 2723053484174360783166929)
                ·
                  refine ⟨2042290113130770587375197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2723053484174360783166929 2042290113130770587375197)
                  ·
                    refine ⟨765858792424038970265699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2042290113130770587375197 765858792424038970265699)
                    ·
                      rfl

theorem cell22_2237257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 2, 3].length) (baseStart_2237257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237257 prefixEnd_2237257 := by exact prefixLift 2237257
  have htrace : WordTrace (prefixWord ++ tailWord_2237257) baseStart_2237257 baseEnd_2237257 := by
    simpa [prefixWord, tailWord_2237257, baseEnd_2237257] using wordTrace_append hprefix tailTrace_2237257
  have hstable : (prefixWord ++ tailWord_2237257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237257).length < 2 ^ (prefixWord ++ tailWord_2237257).sum := by decide
  have hdescent : baseEnd_2237257 < baseStart_2237257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237261 : List Nat := [1, 6, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_2237261 : Nat := 118140960795 + 2237261 * 2 ^ 59
def prefixEnd_2237261 : Nat := 4983230072969 + 3 ^ 40 * 2237261 * 2
def baseEnd_2237261 : Nat := 765860161705784293165687

theorem tailTrace_2237261 : CollatzResearch.WordTrace tailWord_2237261 prefixEnd_2237261 765860161705784293165687 := by
  unfold tailWord_2237261
  simp only [CollatzResearch.WordTrace]
  refine ⟨81599612347792965603871637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54399741565195310402581091 81599612347792965603871637)
  ·
    refine ⟨3824981828802795262681483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81599612347792965603871637 3824981828802795262681483)
    ·
      refine ⟨5737472743204192894022225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3824981828802795262681483 5737472743204192894022225)
      ·
        refine ⟨4303104557403144670516669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5737472743204192894022225 4303104557403144670516669)
        ·
          refine ⟨1613664209026179251443751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4303104557403144670516669 1613664209026179251443751)
          ·
            refine ⟨2420496313539268877165627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1613664209026179251443751 2420496313539268877165627)
            ·
              refine ⟨3630744470308903315748441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2420496313539268877165627 3630744470308903315748441)
              ·
                refine ⟨2723058352731677486811331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3630744470308903315748441 2723058352731677486811331)
                ·
                  refine ⟨4084587529097516230216997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2723058352731677486811331 4084587529097516230216997)
                  ·
                    refine ⟨765860161705784293165687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4084587529097516230216997 765860161705784293165687)
                    ·
                      rfl

theorem cell22_2237261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_2237261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237261 prefixEnd_2237261 := by exact prefixLift 2237261
  have htrace : WordTrace (prefixWord ++ tailWord_2237261) baseStart_2237261 baseEnd_2237261 := by
    simpa [prefixWord, tailWord_2237261, baseEnd_2237261] using wordTrace_append hprefix tailTrace_2237261
  have hstable : (prefixWord ++ tailWord_2237261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237261).length < 2 ^ (prefixWord ++ tailWord_2237261).sum := by decide
  have hdescent : baseEnd_2237261 < baseStart_2237261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237298 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 7]
def baseStart_2237298 : Nat := 118140960795 + 2237298 * 2 ^ 59
def prefixEnd_2237298 : Nat := 4983230072969 + 3 ^ 40 * 2237298 * 2
def baseEnd_2237298 : Nat := 255290942520642843330191

theorem tailTrace_2237298 : CollatzResearch.WordTrace tailWord_2237298 prefixEnd_2237298 255290942520642843330191 := by
  unfold tailWord_2237298
  simp only [CollatzResearch.WordTrace]
  refine ⟨20400240462164730230742137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54400641232439280615312365 20400240462164730230742137)
  ·
    refine ⟨15300180346623547673056603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20400240462164730230742137 15300180346623547673056603)
    ·
      refine ⟨22950270519935321509584905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15300180346623547673056603 22950270519935321509584905)
      ·
        refine ⟨17212702889951491132188679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22950270519935321509584905 17212702889951491132188679)
        ·
          refine ⟨25819054334927236698283019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17212702889951491132188679 25819054334927236698283019)
          ·
            refine ⟨38728581502390855047424529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25819054334927236698283019 38728581502390855047424529)
            ·
              refine ⟨29046436126793141285568397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38728581502390855047424529 29046436126793141285568397)
              ·
                refine ⟨10892413547547427982088149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29046436126793141285568397 10892413547547427982088149)
                ·
                  refine ⟨255290942520642843330191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10892413547547427982088149 255290942520642843330191)
                  ·
                    rfl

theorem cell22_2237298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_2237298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237298 prefixEnd_2237298 := by exact prefixLift 2237298
  have htrace : WordTrace (prefixWord ++ tailWord_2237298) baseStart_2237298 baseEnd_2237298 := by
    simpa [prefixWord, tailWord_2237298, baseEnd_2237298] using wordTrace_append hprefix tailTrace_2237298
  have hstable : (prefixWord ++ tailWord_2237298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237298).length < 2 ^ (prefixWord ++ tailWord_2237298).sum := by decide
  have hdescent : baseEnd_2237298 < baseStart_2237298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237328 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 7, 4]
def baseStart_2237328 : Nat := 118140960795 + 2237328 * 2 ^ 59
def prefixEnd_2237328 : Nat := 4983230072969 + 3 ^ 40 * 2237328 * 2
def baseEnd_2237328 : Nat := 765883097175018451740481

theorem tailTrace_2237328 : CollatzResearch.WordTrace tailWord_2237328 prefixEnd_2237328 765883097175018451740481 := by
  unfold tailWord_2237328
  simp only [CollatzResearch.WordTrace]
  refine ⟨40801028019275118023280319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54401370692366824031040425 40801028019275118023280319)
  ·
    refine ⟨61201542028912677034920479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40801028019275118023280319 61201542028912677034920479)
    ·
      refine ⟨91802313043369015552380719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61201542028912677034920479 91802313043369015552380719)
      ·
        refine ⟨137703469565053523328571079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91802313043369015552380719 137703469565053523328571079)
        ·
          refine ⟨206555204347580284992856619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137703469565053523328571079 206555204347580284992856619)
          ·
            refine ⟨309832806521370427489284929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206555204347580284992856619 309832806521370427489284929)
            ·
              refine ⟨232374604891027820616963697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309832806521370427489284929 232374604891027820616963697)
              ·
                refine ⟨174280953668270865462722773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232374604891027820616963697 174280953668270865462722773)
                ·
                  refine ⟨4084709851600098409282565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 174280953668270865462722773 4084709851600098409282565)
                  ·
                    refine ⟨765883097175018451740481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4084709851600098409282565 765883097175018451740481)
                    ·
                      rfl

theorem cell22_2237328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_2237328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237328 prefixEnd_2237328 := by exact prefixLift 2237328
  have htrace : WordTrace (prefixWord ++ tailWord_2237328) baseStart_2237328 baseEnd_2237328 := by
    simpa [prefixWord, tailWord_2237328, baseEnd_2237328] using wordTrace_append hprefix tailTrace_2237328
  have hstable : (prefixWord ++ tailWord_2237328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237328).length < 2 ^ (prefixWord ++ tailWord_2237328).sum := by decide
  have hdescent : baseEnd_2237328 < baseStart_2237328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237390 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_2237390 : Nat := 118140960795 + 2237390 * 2 ^ 59
def prefixEnd_2237390 : Nat := 4983230072969 + 3 ^ 40 * 2237390 * 2
def baseEnd_2237390 : Nat := 765904321042070956690291

theorem tailTrace_2237390 : CollatzResearch.WordTrace tailWord_2237390 prefixEnd_2237390 765904321042070956690291 := by
  unfold tailWord_2237390
  simp only [CollatzResearch.WordTrace]
  refine ⟨10200539670540702579414703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54402878242883747090211749 10200539670540702579414703)
  ·
    refine ⟨15300809505811053869122055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10200539670540702579414703 15300809505811053869122055)
    ·
      refine ⟨22951214258716580803683083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15300809505811053869122055 22951214258716580803683083)
      ·
        refine ⟨34426821388074871205524625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22951214258716580803683083 34426821388074871205524625)
        ·
          refine ⟨25820116041056153404143469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34426821388074871205524625 25820116041056153404143469)
          ·
            refine ⟨9682543515396057526553801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25820116041056153404143469 9682543515396057526553801)
            ·
              refine ⟨7261907636547043144915351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9682543515396057526553801 7261907636547043144915351)
              ·
                refine ⟨10892861454820564717373027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7261907636547043144915351 10892861454820564717373027)
                ·
                  refine ⟨16339292182230847076059541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10892861454820564717373027 16339292182230847076059541)
                  ·
                    refine ⟨765904321042070956690291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16339292182230847076059541 765904321042070956690291)
                    ·
                      rfl

theorem cell22_2237390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_2237390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237390 prefixEnd_2237390 := by exact prefixLift 2237390
  have htrace : WordTrace (prefixWord ++ tailWord_2237390) baseStart_2237390 baseEnd_2237390 := by
    simpa [prefixWord, tailWord_2237390, baseEnd_2237390] using wordTrace_append hprefix tailTrace_2237390
  have hstable : (prefixWord ++ tailWord_2237390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237390).length < 2 ^ (prefixWord ++ tailWord_2237390).sum := by decide
  have hdescent : baseEnd_2237390 < baseStart_2237390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237394 : List Nat := [3, 2, 2, 3, 1, 1, 3, 3, 4]
def baseStart_2237394 : Nat := 118140960795 + 2237394 * 2 ^ 59
def prefixEnd_2237394 : Nat := 4983230072969 + 3 ^ 40 * 2237394 * 2
def baseEnd_2237394 : Nat := 255301896774605426530093

theorem tailTrace_2237394 : CollatzResearch.WordTrace tailWord_2237394 prefixEnd_2237394 255301896774605426530093 := by
  unfold tailWord_2237394
  simp only [CollatzResearch.WordTrace]
  refine ⟨20401115814077782329615809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54402975504207419545642157 20401115814077782329615809)
  ·
    refine ⟨15300836860558336747211857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20401115814077782329615809 15300836860558336747211857)
    ·
      refine ⟨11475627645418752560408893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15300836860558336747211857 11475627645418752560408893)
      ·
        refine ⟨4303360367032032210153335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11475627645418752560408893 4303360367032032210153335)
        ·
          refine ⟨6455040550548048315230003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4303360367032032210153335 6455040550548048315230003)
          ·
            refine ⟨9682560825822072472845005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6455040550548048315230003 9682560825822072472845005)
            ·
              refine ⟨3630960309683277177316877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9682560825822072472845005 3630960309683277177316877)
              ·
                refine ⟨1361610116131228941493829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3630960309683277177316877 1361610116131228941493829)
                ·
                  refine ⟨255301896774605426530093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1361610116131228941493829 255301896774605426530093)
                  ·
                    rfl

theorem cell22_2237394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_2237394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237394 prefixEnd_2237394 := by exact prefixLift 2237394
  have htrace : WordTrace (prefixWord ++ tailWord_2237394) baseStart_2237394 baseEnd_2237394 := by
    simpa [prefixWord, tailWord_2237394, baseEnd_2237394] using wordTrace_append hprefix tailTrace_2237394
  have hstable : (prefixWord ++ tailWord_2237394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237394).length < 2 ^ (prefixWord ++ tailWord_2237394).sum := by decide
  have hdescent : baseEnd_2237394 < baseStart_2237394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237405 : List Nat := [1, 4, 3, 1, 2, 1, 10]
def baseStart_2237405 : Nat := 118140960795 + 2237405 * 2 ^ 59
def prefixEnd_2237405 : Nat := 4983230072969 + 3 ^ 40 * 2237405 * 2
def baseEnd_2237405 : Nat := 28367016883282071020935

theorem tailTrace_2237405 : CollatzResearch.WordTrace tailWord_2237405 prefixEnd_2237405 28367016883282071020935 := by
  unfold tailWord_2237405
  simp only [CollatzResearch.WordTrace]
  refine ⟨81604864459271278197113669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54403242972847518798075779 81604864459271278197113669)
  ·
    refine ⟨15300912086113364661958813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81604864459271278197113669 15300912086113364661958813)
    ·
      refine ⟨5737842032292511748234555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15300912086113364661958813 5737842032292511748234555)
      ·
        refine ⟨8606763048438767622351833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5737842032292511748234555 8606763048438767622351833)
        ·
          refine ⟨6455072286329075716763875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8606763048438767622351833 6455072286329075716763875)
          ·
            refine ⟨9682608429493613575145813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6455072286329075716763875 9682608429493613575145813)
            ·
              refine ⟨28367016883282071020935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9682608429493613575145813 28367016883282071020935)
              ·
                rfl

theorem cell22_2237405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 10].length) (baseStart_2237405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237405 prefixEnd_2237405 := by exact prefixLift 2237405
  have htrace : WordTrace (prefixWord ++ tailWord_2237405) baseStart_2237405 baseEnd_2237405 := by
    simpa [prefixWord, tailWord_2237405, baseEnd_2237405] using wordTrace_append hprefix tailTrace_2237405
  have hstable : (prefixWord ++ tailWord_2237405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237405).length < 2 ^ (prefixWord ++ tailWord_2237405).sum := by decide
  have hdescent : baseEnd_2237405 < baseStart_2237405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237407 : List Nat := [1, 1, 2, 3, 5, 1, 1, 2, 2, 4]
def baseStart_2237407 : Nat := 118140960795 + 2237407 * 2 ^ 59
def prefixEnd_2237407 : Nat := 4983230072969 + 3 ^ 40 * 2237407 * 2
def baseEnd_2237407 : Nat := 765910140489488579015239

theorem tailTrace_2237407 : CollatzResearch.WordTrace tailWord_2237407 prefixEnd_2237407 765910140489488579015239 := by
  unfold tailWord_2237407
  simp only [CollatzResearch.WordTrace]
  refine ⟨81604937405264032538686475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54403291603509355025790983 81604937405264032538686475)
  ·
    refine ⟨122407406107896048808029713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81604937405264032538686475 122407406107896048808029713)
    ·
      refine ⟨91805554580922036606022285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122407406107896048808029713 91805554580922036606022285)
      ·
        refine ⟨34427082967845763727258357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91805554580922036606022285 34427082967845763727258357)
        ·
          refine ⟨3227539028235540349430471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34427082967845763727258357 3227539028235540349430471)
          ·
            refine ⟨4841308542353310524145707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3227539028235540349430471 4841308542353310524145707)
            ·
              refine ⟨7261962813529965786218561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4841308542353310524145707 7261962813529965786218561)
              ·
                refine ⟨5446472110147474339663921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7261962813529965786218561 5446472110147474339663921)
                ·
                  refine ⟨4084854082610605754747941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5446472110147474339663921 4084854082610605754747941)
                  ·
                    refine ⟨765910140489488579015239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4084854082610605754747941 765910140489488579015239)
                    ·
                      rfl

theorem cell22_2237407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 4].length) (baseStart_2237407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237407 prefixEnd_2237407 := by exact prefixLift 2237407
  have htrace : WordTrace (prefixWord ++ tailWord_2237407) baseStart_2237407 baseEnd_2237407 := by
    simpa [prefixWord, tailWord_2237407, baseEnd_2237407] using wordTrace_append hprefix tailTrace_2237407
  have hstable : (prefixWord ++ tailWord_2237407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237407).length < 2 ^ (prefixWord ++ tailWord_2237407).sum := by decide
  have hdescent : baseEnd_2237407 < baseStart_2237407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237422 : List Nat := [4, 1, 2, 1, 4, 1, 2, 7]
def baseStart_2237422 : Nat := 118140960795 + 2237422 * 2 ^ 59
def prefixEnd_2237422 : Nat := 4983230072969 + 3 ^ 40 * 2237422 * 2
def baseEnd_2237422 : Nat := 85101697255114837765577

theorem tailTrace_2237422 : CollatzResearch.WordTrace tailWord_2237422 prefixEnd_2237422 85101697255114837765577 := by
  unfold tailWord_2237422
  simp only [CollatzResearch.WordTrace]
  refine ⟨10200685562526211262560315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54403656333473126733655013 10200685562526211262560315)
  ·
    refine ⟨15301028343789316893840473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10200685562526211262560315 15301028343789316893840473)
    ·
      refine ⟨11475771257841987670380355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15301028343789316893840473 11475771257841987670380355)
      ·
        refine ⟨17213656886762981505570533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11475771257841987670380355 17213656886762981505570533)
        ·
          refine ⟨3227560666268059032294475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17213656886762981505570533 3227560666268059032294475)
          ·
            refine ⟨4841340999402088548441713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3227560666268059032294475 4841340999402088548441713)
            ·
              refine ⟨3631005749551566411331285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4841340999402088548441713 3631005749551566411331285)
              ·
                refine ⟨85101697255114837765577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3631005749551566411331285 85101697255114837765577)
                ·
                  rfl

theorem cell22_2237422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_2237422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237422 prefixEnd_2237422 := by exact prefixLift 2237422
  have htrace : WordTrace (prefixWord ++ tailWord_2237422) baseStart_2237422 baseEnd_2237422 := by
    simpa [prefixWord, tailWord_2237422, baseEnd_2237422] using wordTrace_append hprefix tailTrace_2237422
  have hstable : (prefixWord ++ tailWord_2237422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237422).length < 2 ^ (prefixWord ++ tailWord_2237422).sum := by decide
  have hdescent : baseEnd_2237422 < baseStart_2237422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237426 : List Nat := [3, 2, 1, 5, 1, 1, 1, 3, 2, 3]
def baseStart_2237426 : Nat := 118140960795 + 2237426 * 2 ^ 59
def prefixEnd_2237426 : Nat := 4983230072969 + 3 ^ 40 * 2237426 * 2
def baseEnd_2237426 : Nat := 765916644577778862790181

theorem tailTrace_2237426 : CollatzResearch.WordTrace tailWord_2237426 prefixEnd_2237426 765916644577778862790181 := by
  unfold tailWord_2237426
  simp only [CollatzResearch.WordTrace]
  refine ⟨20401407598048799695907033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54403753594796799189085421 20401407598048799695907033)
  ·
    refine ⟨15301055698536599771930275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20401407598048799695907033 15301055698536599771930275)
    ·
      refine ⟨22951583547804899657895413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15301055698536599771930275 22951583547804899657895413)
      ·
        refine ⟨2151710957606709342927695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22951583547804899657895413 2151710957606709342927695)
        ·
          refine ⟨3227566436410064014391543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2151710957606709342927695 3227566436410064014391543)
          ·
            refine ⟨4841349654615096021587315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3227566436410064014391543 4841349654615096021587315)
            ·
              refine ⟨7262024481922644032380973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4841349654615096021587315 7262024481922644032380973)
              ·
                refine ⟨2723259180720991512142865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7262024481922644032380973 2723259180720991512142865)
                ·
                  refine ⟨2042444385540743634107149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2723259180720991512142865 2042444385540743634107149)
                  ·
                    refine ⟨765916644577778862790181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2042444385540743634107149 765916644577778862790181)
                    ·
                      rfl

theorem cell22_2237426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_2237426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237426 prefixEnd_2237426 := by exact prefixLift 2237426
  have htrace : WordTrace (prefixWord ++ tailWord_2237426) baseStart_2237426 baseEnd_2237426 := by
    simpa [prefixWord, tailWord_2237426, baseEnd_2237426] using wordTrace_append hprefix tailTrace_2237426
  have hstable : (prefixWord ++ tailWord_2237426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237426).length < 2 ^ (prefixWord ++ tailWord_2237426).sum := by decide
  have hdescent : baseEnd_2237426 < baseStart_2237426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237471 : List Nat := [1, 1, 2, 4, 1, 3, 4, 2, 1, 3]
def baseStart_2237471 : Nat := 118140960795 + 2237471 * 2 ^ 59
def prefixEnd_2237471 : Nat := 4983230072969 + 3 ^ 40 * 2237471 * 2
def baseEnd_2237471 : Nat := 765932048997413745415043

theorem tailTrace_2237471 : CollatzResearch.WordTrace tailWord_2237471 prefixEnd_2237471 765932048997413745415043 := by
  unfold tailWord_2237471
  simp only [CollatzResearch.WordTrace]
  refine ⟨81607271677032171469016267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54404847784688114312677511 81607271677032171469016267)
  ·
    refine ⟨122410907515548257203524401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81607271677032171469016267 122410907515548257203524401)
    ·
      refine ⟨91808180636661192902643301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122410907515548257203524401 91808180636661192902643301)
      ·
        refine ⟨17214033869373973669245619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91808180636661192902643301 17214033869373973669245619)
        ·
          refine ⟨25821050804060960503868429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17214033869373973669245619 25821050804060960503868429)
          ·
            refine ⟨9682894051522860188950661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25821050804060960503868429 9682894051522860188950661)
            ·
              refine ⟨1815542634660536285428249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9682894051522860188950661 1815542634660536285428249)
              ·
                refine ⟨1361656975995402214071187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1815542634660536285428249 1361656975995402214071187)
                ·
                  refine ⟨2042485463993103321106781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1361656975995402214071187 2042485463993103321106781)
                  ·
                    refine ⟨765932048997413745415043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2042485463993103321106781 765932048997413745415043)
                    ·
                      rfl

theorem cell22_2237471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 1, 3].length) (baseStart_2237471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237471 prefixEnd_2237471 := by exact prefixLift 2237471
  have htrace : WordTrace (prefixWord ++ tailWord_2237471) baseStart_2237471 baseEnd_2237471 := by
    simpa [prefixWord, tailWord_2237471, baseEnd_2237471] using wordTrace_append hprefix tailTrace_2237471
  have hstable : (prefixWord ++ tailWord_2237471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237471).length < 2 ^ (prefixWord ++ tailWord_2237471).sum := by decide
  have hdescent : baseEnd_2237471 < baseStart_2237471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237497 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 3, 4]
def baseStart_2237497 : Nat := 118140960795 + 2237497 * 2 ^ 59
def prefixEnd_2237497 : Nat := 4983230072969 + 3 ^ 40 * 2237497 * 2
def baseEnd_2237497 : Nat := 765940949328758344264963

theorem tailTrace_2237497 : CollatzResearch.WordTrace tailWord_2237497 prefixEnd_2237497 765940949328758344264963 := by
  unfold tailWord_2237497
  simp only [CollatzResearch.WordTrace]
  refine ⟨81608219974937977909462745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54405479983291985272975163 81608219974937977909462745)
  ·
    refine ⟨61206164981203483432097059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81608219974937977909462745 61206164981203483432097059)
    ·
      refine ⟨91809247471805225148145589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61206164981203483432097059 91809247471805225148145589)
      ·
        refine ⟨8607116950481739857638649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91809247471805225148145589 8607116950481739857638649)
        ·
          refine ⟨6455337712861304893228987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8607116950481739857638649 6455337712861304893228987)
          ·
            refine ⟨9683006569291957339843481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6455337712861304893228987 9683006569291957339843481)
            ·
              refine ⟨7262254926968968004882611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9683006569291957339843481 7262254926968968004882611)
              ·
                refine ⟨10893382390453452007323917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7262254926968968004882611 10893382390453452007323917)
                ·
                  refine ⟨4085018396420044502746469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10893382390453452007323917 4085018396420044502746469)
                  ·
                    refine ⟨765940949328758344264963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4085018396420044502746469 765940949328758344264963)
                    ·
                      rfl

theorem cell22_2237497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_2237497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237497 prefixEnd_2237497 := by exact prefixLift 2237497
  have htrace : WordTrace (prefixWord ++ tailWord_2237497) baseStart_2237497 baseEnd_2237497 := by
    simpa [prefixWord, tailWord_2237497, baseEnd_2237497] using wordTrace_append hprefix tailTrace_2237497
  have hstable : (prefixWord ++ tailWord_2237497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237497).length < 2 ^ (prefixWord ++ tailWord_2237497).sum := by decide
  have hdescent : baseEnd_2237497 < baseStart_2237497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237514 : List Nat := [3, 1, 2, 1, 1, 2, 6, 1, 1, 4]
def baseStart_2237514 : Nat := 118140960795 + 2237514 * 2 ^ 59
def prefixEnd_2237514 : Nat := 4983230072969 + 3 ^ 40 * 2237514 * 2
def baseEnd_2237514 : Nat := 765946768776175966589911

theorem tailTrace_2237514 : CollatzResearch.WordTrace tailWord_2237514 prefixEnd_2237514 765946768776175966589911 := by
  unfold tailWord_2237514
  simp only [CollatzResearch.WordTrace]
  refine ⟨20402210003969097453207899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54405893343917593208554397 20402210003969097453207899)
  ·
    refine ⟨30603315005953646179811849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20402210003969097453207899 30603315005953646179811849)
    ·
      refine ⟨22952486254465234634858887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30603315005953646179811849 22952486254465234634858887)
      ·
        refine ⟨34428729381697851952288331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22952486254465234634858887 34428729381697851952288331)
        ·
          refine ⟨51643094072546777928432497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34428729381697851952288331 51643094072546777928432497)
          ·
            refine ⟨38732320554410083446324373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51643094072546777928432497 38732320554410083446324373)
            ·
              refine ⟨1815577525987972661546455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38732320554410083446324373 1815577525987972661546455)
              ·
                refine ⟨2723366288981958992319683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1815577525987972661546455 2723366288981958992319683)
                ·
                  refine ⟨4085049433472938488479525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2723366288981958992319683 4085049433472938488479525)
                  ·
                    refine ⟨765946768776175966589911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4085049433472938488479525 765946768776175966589911)
                    ·
                      rfl

theorem cell22_2237514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_2237514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237514 prefixEnd_2237514 := by exact prefixLift 2237514
  have htrace : WordTrace (prefixWord ++ tailWord_2237514) baseStart_2237514 baseEnd_2237514 := by
    simpa [prefixWord, tailWord_2237514, baseEnd_2237514] using wordTrace_append hprefix tailTrace_2237514
  have hstable : (prefixWord ++ tailWord_2237514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237514).length < 2 ^ (prefixWord ++ tailWord_2237514).sum := by decide
  have hdescent : baseEnd_2237514 < baseStart_2237514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237540 : List Nat := [2, 3, 1, 1, 2, 1, 1, 11]
def baseStart_2237540 : Nat := 118140960795 + 2237540 * 2 ^ 59
def prefixEnd_2237540 : Nat := 4983230072969 + 3 ^ 40 * 2237540 * 2
def baseEnd_2237540 : Nat := 85106185456391173937759

theorem tailTrace_2237540 : CollatzResearch.WordTrace tailWord_2237540 prefixEnd_2237540 85106185456391173937759 := by
  unfold tailWord_2237540
  simp only [CollatzResearch.WordTrace]
  refine ⟨40804894156891098126639037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54406525542521464168852049 40804894156891098126639037)
  ·
    refine ⟨15301835308834161797489639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40804894156891098126639037 15301835308834161797489639)
    ·
      refine ⟨22952752963251242696234459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15301835308834161797489639 22952752963251242696234459)
      ·
        refine ⟨34429129444876864044351689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22952752963251242696234459 34429129444876864044351689)
        ·
          refine ⟨25821847083657648033263767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34429129444876864044351689 25821847083657648033263767)
          ·
            refine ⟨38732770625486472049895651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25821847083657648033263767 38732770625486472049895651)
            ·
              refine ⟨58099155938229708074843477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38732770625486472049895651 58099155938229708074843477)
              ·
                refine ⟨85106185456391173937759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 58099155938229708074843477 85106185456391173937759)
                ·
                  rfl

theorem cell22_2237540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 11].length) (baseStart_2237540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237540 prefixEnd_2237540 := by exact prefixLift 2237540
  have htrace : WordTrace (prefixWord ++ tailWord_2237540) baseStart_2237540 baseEnd_2237540 := by
    simpa [prefixWord, tailWord_2237540, baseEnd_2237540] using wordTrace_append hprefix tailTrace_2237540
  have hstable : (prefixWord ++ tailWord_2237540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237540).length < 2 ^ (prefixWord ++ tailWord_2237540).sum := by decide
  have hdescent : baseEnd_2237540 < baseStart_2237540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237636 : List Nat := [2, 3, 3, 1, 3, 1, 2, 2, 5]
def baseStart_2237636 : Nat := 118140960795 + 2237636 * 2 ^ 59
def prefixEnd_2237636 : Nat := 4983230072969 + 3 ^ 40 * 2237636 * 2
def baseEnd_2237636 : Nat := 255329510623136105013179

theorem tailTrace_2237636 : CollatzResearch.WordTrace tailWord_2237636 prefixEnd_2237636 255329510623136105013179 := by
  unfold tailWord_2237636
  simp only [CollatzResearch.WordTrace]
  refine ⟨40806644860717202324386381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54408859814289603099181841 40806644860717202324386381)
  ·
    refine ⟨15302491822768950871644893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40806644860717202324386381 15302491822768950871644893)
    ·
      refine ⟨5738434433538356576866835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15302491822768950871644893 5738434433538356576866835)
      ·
        refine ⟨8607651650307534865300253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5738434433538356576866835 8607651650307534865300253)
        ·
          refine ⟨3227869368865325574487595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8607651650307534865300253 3227869368865325574487595)
          ·
            refine ⟨4841804053297988361731393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3227869368865325574487595 4841804053297988361731393)
            ·
              refine ⟨3631353039973491271298545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4841804053297988361731393 3631353039973491271298545)
              ·
                refine ⟨2723514779980118453473909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3631353039973491271298545 2723514779980118453473909)
                ·
                  refine ⟨255329510623136105013179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2723514779980118453473909 255329510623136105013179)
                  ·
                    rfl

theorem cell22_2237636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_2237636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237636 prefixEnd_2237636 := by exact prefixLift 2237636
  have htrace : WordTrace (prefixWord ++ tailWord_2237636) baseStart_2237636 baseEnd_2237636 := by
    simpa [prefixWord, tailWord_2237636, baseEnd_2237636] using wordTrace_append hprefix tailTrace_2237636
  have hstable : (prefixWord ++ tailWord_2237636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237636).length < 2 ^ (prefixWord ++ tailWord_2237636).sum := by decide
  have hdescent : baseEnd_2237636 < baseStart_2237636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237754 : List Nat := [3, 1, 1, 1, 4, 1, 2, 4, 5]
def baseStart_2237754 : Nat := 118140960795 + 2237754 * 2 ^ 59
def prefixEnd_2237754 : Nat := 4983230072969 + 3 ^ 40 * 2237754 * 2
def baseEnd_2237754 : Nat := 255342975226965113529725

theorem tailTrace_2237754 : CollatzResearch.WordTrace tailWord_2237754 prefixEnd_2237754 255342975226965113529725 := by
  unfold tailWord_2237754
  simp only [CollatzResearch.WordTrace]
  refine ⟨20404398383751727700392079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54411729023337940534378877 20404398383751727700392079)
  ·
    refine ⟨30606597575627591550588119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20404398383751727700392079 30606597575627591550588119)
    ·
      refine ⟨45909896363441387325882179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30606597575627591550588119 45909896363441387325882179)
      ·
        refine ⟨68864844545162080988823269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45909896363441387325882179 68864844545162080988823269)
        ·
          refine ⟨12912158352217890185404363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68864844545162080988823269 12912158352217890185404363)
          ·
            refine ⟨19368237528326835278106545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12912158352217890185404363 19368237528326835278106545)
            ·
              refine ⟨14526178146245126458579909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19368237528326835278106545 14526178146245126458579909)
              ·
                refine ⟨2723658402420961210983733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14526178146245126458579909 2723658402420961210983733)
                ·
                  refine ⟨255342975226965113529725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2723658402420961210983733 255342975226965113529725)
                  ·
                    rfl

theorem cell22_2237754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_2237754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237754 prefixEnd_2237754 := by exact prefixLift 2237754
  have htrace : WordTrace (prefixWord ++ tailWord_2237754) baseStart_2237754 baseEnd_2237754 := by
    simpa [prefixWord, tailWord_2237754, baseEnd_2237754] using wordTrace_append hprefix tailTrace_2237754
  have hstable : (prefixWord ++ tailWord_2237754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237754).length < 2 ^ (prefixWord ++ tailWord_2237754).sum := by decide
  have hdescent : baseEnd_2237754 < baseStart_2237754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237784 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 3, 4]
def baseStart_2237784 : Nat := 118140960795 + 2237784 * 2 ^ 59
def prefixEnd_2237784 : Nat := 4983230072969 + 3 ^ 40 * 2237784 * 2
def baseEnd_2237784 : Nat := 766039195293985262339083

theorem tailTrace_2237784 : CollatzResearch.WordTrace tailWord_2237784 prefixEnd_2237784 766039195293985262339083 := by
  unfold tailWord_2237784
  simp only [CollatzResearch.WordTrace]
  refine ⟨40809343862449112962580203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54412458483265483950106937 40809343862449112962580203)
  ·
    refine ⟨61214015793673669443870305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40809343862449112962580203 61214015793673669443870305)
    ·
      refine ⟨45910511845255252082902729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61214015793673669443870305 45910511845255252082902729)
      ·
        refine ⟨34432883883941439062177047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45910511845255252082902729 34432883883941439062177047)
        ·
          refine ⟨51649325825912158593265571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34432883883941439062177047 51649325825912158593265571)
          ·
            refine ⟨77473988738868237889898357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51649325825912158593265571 77473988738868237889898357)
            ·
              refine ⟨7263186444268897302177971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77473988738868237889898357 7263186444268897302177971)
              ·
                refine ⟨10894779666403345953266957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7263186444268897302177971 10894779666403345953266957)
                ·
                  refine ⟨4085542374901254732475109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10894779666403345953266957 4085542374901254732475109)
                  ·
                    refine ⟨766039195293985262339083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4085542374901254732475109 766039195293985262339083)
                    ·
                      rfl

theorem cell22_2237784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_2237784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237784 prefixEnd_2237784 := by exact prefixLift 2237784
  have htrace : WordTrace (prefixWord ++ tailWord_2237784) baseStart_2237784 baseEnd_2237784 := by
    simpa [prefixWord, tailWord_2237784, baseEnd_2237784] using wordTrace_append hprefix tailTrace_2237784
  have hstable : (prefixWord ++ tailWord_2237784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237784).length < 2 ^ (prefixWord ++ tailWord_2237784).sum := by decide
  have hdescent : baseEnd_2237784 < baseStart_2237784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237829 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 4, 4]
def baseStart_2237829 : Nat := 118140960795 + 2237829 * 2 ^ 59
def prefixEnd_2237829 : Nat := 4983230072969 + 3 ^ 40 * 2237829 * 2
def baseEnd_2237829 : Nat := 766054599713620144963945

theorem tailTrace_2237829 : CollatzResearch.WordTrace tailWord_2237829 prefixEnd_2237829 766054599713620144963945 := by
  unfold tailWord_2237829
  simp only [CollatzResearch.WordTrace]
  refine ⟨81620329009735198610548541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54413552673156799073699027 81620329009735198610548541)
  ·
    refine ⟨30607623378650699478955703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81620329009735198610548541 30607623378650699478955703)
    ·
      refine ⟨45911435067976049218433555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30607623378650699478955703 45911435067976049218433555)
      ·
        refine ⟨68867152601964073827650333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45911435067976049218433555 68867152601964073827650333)
        ·
          refine ⟨25825182225736527685368875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68867152601964073827650333 25825182225736527685368875)
          ·
            refine ⟨38737773338604791528053313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25825182225736527685368875 38737773338604791528053313)
            ·
              refine ⟨29053330003953593646039985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38737773338604791528053313 29053330003953593646039985)
              ·
                refine ⟨21789997502965195234529989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29053330003953593646039985 21789997502965195234529989)
                ·
                  refine ⟨4085624531805974106474373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21789997502965195234529989 4085624531805974106474373)
                  ·
                    refine ⟨766054599713620144963945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4085624531805974106474373 766054599713620144963945)
                    ·
                      rfl

theorem cell22_2237829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_2237829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237829 prefixEnd_2237829 := by exact prefixLift 2237829
  have htrace : WordTrace (prefixWord ++ tailWord_2237829) baseStart_2237829 baseEnd_2237829 := by
    simpa [prefixWord, tailWord_2237829, baseEnd_2237829] using wordTrace_append hprefix tailTrace_2237829
  have hstable : (prefixWord ++ tailWord_2237829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237829).length < 2 ^ (prefixWord ++ tailWord_2237829).sum := by decide
  have hdescent : baseEnd_2237829 < baseStart_2237829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237831 : List Nat := [1, 1, 4, 2, 2, 3, 2, 1, 1, 5]
def baseStart_2237831 : Nat := 118140960795 + 2237831 * 2 ^ 59
def prefixEnd_2237831 : Nat := 4983230072969 + 3 ^ 40 * 2237831 * 2
def baseEnd_2237831 : Nat := 766055284354492806413939

theorem tailTrace_2237831 : CollatzResearch.WordTrace tailWord_2237831 prefixEnd_2237831 766055284354492806413939 := by
  unfold tailWord_2237831
  simp only [CollatzResearch.WordTrace]
  refine ⟨81620401955727952952121347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54413601303818635301414231 81620401955727952952121347)
  ·
    refine ⟨122430602933591929428182021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81620401955727952952121347 122430602933591929428182021)
    ·
      refine ⟨22955738050048486767784129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122430602933591929428182021 22955738050048486767784129)
      ·
        refine ⟨17216803537536365075838097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22955738050048486767784129 17216803537536365075838097)
        ·
          refine ⟨12912602653152273806878573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17216803537536365075838097 12912602653152273806878573)
          ·
            refine ⟨4842225994932102677579465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12912602653152273806878573 4842225994932102677579465)
            ·
              refine ⟨3631669496199077008184599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4842225994932102677579465 3631669496199077008184599)
              ·
                refine ⟨5447504244298615512276899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3631669496199077008184599 5447504244298615512276899)
                ·
                  refine ⟨8171256366447923268415349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5447504244298615512276899 8171256366447923268415349)
                  ·
                    refine ⟨766055284354492806413939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8171256366447923268415349 766055284354492806413939)
                    ·
                      rfl

theorem cell22_2237831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_2237831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237831 prefixEnd_2237831 := by exact prefixLift 2237831
  have htrace : WordTrace (prefixWord ++ tailWord_2237831) baseStart_2237831 baseEnd_2237831 := by
    simpa [prefixWord, tailWord_2237831, baseEnd_2237831] using wordTrace_append hprefix tailTrace_2237831
  have hstable : (prefixWord ++ tailWord_2237831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237831).length < 2 ^ (prefixWord ++ tailWord_2237831).sum := by decide
  have hdescent : baseEnd_2237831 < baseStart_2237831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237852 : List Nat := [2, 2, 3, 4, 1, 2, 2, 1, 1, 4]
def baseStart_2237852 : Nat := 118140960795 + 2237852 * 2 ^ 59
def prefixEnd_2237852 : Nat := 4983230072969 + 3 ^ 40 * 2237852 * 2
def baseEnd_2237852 : Nat := 766062473083655751638875

theorem tailTrace_2237852 : CollatzResearch.WordTrace tailWord_2237852 prefixEnd_2237852 766062473083655751638875 := by
  unfold tailWord_2237852
  simp only [CollatzResearch.WordTrace]
  refine ⟨40810583944325936769317905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54414111925767915692423873 40810583944325936769317905)
  ·
    refine ⟨30607937958244452576988429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40810583944325936769317905 30607937958244452576988429)
    ·
      refine ⟨11477976734341669716370661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30607937958244452576988429 11477976734341669716370661)
      ·
        refine ⟨2152120637689063071819499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11477976734341669716370661 2152120637689063071819499)
        ·
          refine ⟨3228180956533594607729249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2152120637689063071819499 3228180956533594607729249)
          ·
            refine ⟨2421135717400195955796937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3228180956533594607729249 2421135717400195955796937)
            ·
              refine ⟨1815851788050146966847703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2421135717400195955796937 1815851788050146966847703)
              ·
                refine ⟨2723777682075220450271555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1815851788050146966847703 2723777682075220450271555)
                ·
                  refine ⟨4085666523112830675407333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2723777682075220450271555 4085666523112830675407333)
                  ·
                    refine ⟨766062473083655751638875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4085666523112830675407333 766062473083655751638875)
                    ·
                      rfl

theorem cell22_2237852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_2237852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237852 prefixEnd_2237852 := by exact prefixLift 2237852
  have htrace : WordTrace (prefixWord ++ tailWord_2237852) baseStart_2237852 baseEnd_2237852 := by
    simpa [prefixWord, tailWord_2237852, baseEnd_2237852] using wordTrace_append hprefix tailTrace_2237852
  have hstable : (prefixWord ++ tailWord_2237852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237852).length < 2 ^ (prefixWord ++ tailWord_2237852).sum := by decide
  have hdescent : baseEnd_2237852 < baseStart_2237852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237874 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_2237874 : Nat := 118140960795 + 2237874 * 2 ^ 59
def prefixEnd_2237874 : Nat := 4983230072969 + 3 ^ 40 * 2237874 * 2
def baseEnd_2237874 : Nat := 766070004133255027588807

theorem tailTrace_2237874 : CollatzResearch.WordTrace tailWord_2237874 prefixEnd_2237874 766070004133255027588807 := by
  unfold tailWord_2237874
  simp only [CollatzResearch.WordTrace]
  refine ⟨20405492573643042823984169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54414646863048114197291117 20405492573643042823984169)
  ·
    refine ⟨15304119430232282117988127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20405492573643042823984169 15304119430232282117988127)
    ·
      refine ⟨22956179145348423176982191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15304119430232282117988127 22956179145348423176982191)
      ·
        refine ⟨34434268718022634765473287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22956179145348423176982191 34434268718022634765473287)
        ·
          refine ⟨51651403077033952148209931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34434268718022634765473287 51651403077033952148209931)
          ·
            refine ⟨77477104615550928222314897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51651403077033952148209931 77477104615550928222314897)
            ·
              refine ⟨58107828461663196166736173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77477104615550928222314897 58107828461663196166736173)
              ·
                refine ⟨21790435673123698562526065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58107828461663196166736173 21790435673123698562526065)
                ·
                  refine ⟨16342826754842773921894549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21790435673123698562526065 16342826754842773921894549)
                  ·
                    refine ⟨766070004133255027588807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16342826754842773921894549 766070004133255027588807)
                    ·
                      rfl

theorem cell22_2237874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_2237874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237874 prefixEnd_2237874 := by exact prefixLift 2237874
  have htrace : WordTrace (prefixWord ++ tailWord_2237874) baseStart_2237874 baseEnd_2237874 := by
    simpa [prefixWord, tailWord_2237874, baseEnd_2237874] using wordTrace_append hprefix tailTrace_2237874
  have hstable : (prefixWord ++ tailWord_2237874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237874).length < 2 ^ (prefixWord ++ tailWord_2237874).sum := by decide
  have hdescent : baseEnd_2237874 < baseStart_2237874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237927 : List Nat := [1, 1, 5, 2, 1, 3, 3, 2, 1, 3]
def baseStart_2237927 : Nat := 118140960795 + 2237927 * 2 ^ 59
def prefixEnd_2237927 : Nat := 4983230072969 + 3 ^ 40 * 2237927 * 2
def baseEnd_2237927 : Nat := 766088147116380556013645

theorem tailTrace_2237927 : CollatzResearch.WordTrace tailWord_2237927 prefixEnd_2237927 766088147116380556013645 := by
  unfold tailWord_2237927
  simp only [CollatzResearch.WordTrace]
  refine ⟨81623903363380161347616035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54415935575586774231744023 81623903363380161347616035)
  ·
    refine ⟨122435855045070242021424053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81623903363380161347616035 122435855045070242021424053)
    ·
      refine ⟨11478361410475335189508505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122435855045070242021424053 11478361410475335189508505)
      ·
        refine ⟨8608771057856501392131379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11478361410475335189508505 8608771057856501392131379)
        ·
          refine ⟨12913156586784752088197069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8608771057856501392131379 12913156586784752088197069)
          ·
            refine ⟨4842433720044282033073901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12913156586784752088197069 4842433720044282033073901)
            ·
              refine ⟨1815912645016605762402713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4842433720044282033073901 1815912645016605762402713)
              ·
                refine ⟨1361934483762454321802035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1815912645016605762402713 1361934483762454321802035)
                ·
                  refine ⟨2042901725643681482703053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1361934483762454321802035 2042901725643681482703053)
                  ·
                    refine ⟨766088147116380556013645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2042901725643681482703053 766088147116380556013645)
                    ·
                      rfl

theorem cell22_2237927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_2237927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237927 prefixEnd_2237927 := by exact prefixLift 2237927
  have htrace : WordTrace (prefixWord ++ tailWord_2237927) baseStart_2237927 baseEnd_2237927 := by
    simpa [prefixWord, tailWord_2237927, baseEnd_2237927] using wordTrace_append hprefix tailTrace_2237927
  have hstable : (prefixWord ++ tailWord_2237927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237927).length < 2 ^ (prefixWord ++ tailWord_2237927).sum := by decide
  have hdescent : baseEnd_2237927 < baseStart_2237927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237953 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 3, 4]
def baseStart_2237953 : Nat := 118140960795 + 2237953 * 2 ^ 59
def prefixEnd_2237953 : Nat := 4983230072969 + 3 ^ 40 * 2237953 * 2
def baseEnd_2237953 : Nat := 766097047447725154863565

theorem tailTrace_2237953 : CollatzResearch.WordTrace tailWord_2237953 prefixEnd_2237953 766097047447725154863565 := by
  unfold tailWord_2237953
  simp only [CollatzResearch.WordTrace]
  refine ⟨81624851661285967788062513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54416567774190645192041675 81624851661285967788062513)
  ·
    refine ⟨61218638745964475841046885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81624851661285967788062513 61218638745964475841046885)
    ·
      refine ⟨11478494764868339220196291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61218638745964475841046885 11478494764868339220196291)
      ·
        refine ⟨17217742147302508830294437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11478494764868339220196291 17217742147302508830294437)
        ·
          refine ⟨3228326652619220405680207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17217742147302508830294437 3228326652619220405680207)
          ·
            refine ⟨4842489978928830608520311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3228326652619220405680207 4842489978928830608520311)
            ·
              refine ⟨7263734968393245912780467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4842489978928830608520311 7263734968393245912780467)
              ·
                refine ⟨10895602452589868869170701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7263734968393245912780467 10895602452589868869170701)
                ·
                  refine ⟨4085850919721200825939013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10895602452589868869170701 4085850919721200825939013)
                  ·
                    refine ⟨766097047447725154863565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4085850919721200825939013 766097047447725154863565)
                    ·
                      rfl

theorem cell22_2237953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_2237953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237953 prefixEnd_2237953 := by exact prefixLift 2237953
  have htrace : WordTrace (prefixWord ++ tailWord_2237953) baseStart_2237953 baseEnd_2237953 := by
    simpa [prefixWord, tailWord_2237953, baseEnd_2237953] using wordTrace_append hprefix tailTrace_2237953
  have hstable : (prefixWord ++ tailWord_2237953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237953).length < 2 ^ (prefixWord ++ tailWord_2237953).sum := by decide
  have hdescent : baseEnd_2237953 < baseStart_2237953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237983 : List Nat := [1, 1, 2, 4, 1, 1, 3, 4, 2, 3]
def baseStart_2237983 : Nat := 118140960795 + 2237983 * 2 ^ 59
def prefixEnd_2237983 : Nat := 4983230072969 + 3 ^ 40 * 2237983 * 2
def baseEnd_2237983 : Nat := 766107317060815076613473

theorem tailTrace_2237983 : CollatzResearch.WordTrace tailWord_2237983 prefixEnd_2237983 766107317060815076613473 := by
  unfold tailWord_2237983
  simp only [CollatzResearch.WordTrace]
  refine ⟨81625945851177282911654603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54417297234118188607769735 81625945851177282911654603)
  ·
    refine ⟨122438918776765924367481905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81625945851177282911654603 122438918776765924367481905)
    ·
      refine ⟨91829189082574443275611429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122438918776765924367481905 91829189082574443275611429)
      ·
        refine ⟨17217972952982708114177143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91829189082574443275611429 17217972952982708114177143)
        ·
          refine ⟨25826959429474062171265715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17217972952982708114177143 25826959429474062171265715)
          ·
            refine ⟨38740439144211093256898573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25826959429474062171265715 38740439144211093256898573)
            ·
              refine ⟨14527664679079159971336965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38740439144211093256898573 14527664679079159971336965)
              ·
                refine ⟨2723937127327342494625681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14527664679079159971336965 2723937127327342494625681)
                ·
                  refine ⟨2042952845495506870969261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2723937127327342494625681 2042952845495506870969261)
                  ·
                    refine ⟨766107317060815076613473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2042952845495506870969261 766107317060815076613473)
                    ·
                      rfl

theorem cell22_2237983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 3].length) (baseStart_2237983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237983 prefixEnd_2237983 := by exact prefixLift 2237983
  have htrace : WordTrace (prefixWord ++ tailWord_2237983) baseStart_2237983 baseEnd_2237983 := by
    simpa [prefixWord, tailWord_2237983, baseEnd_2237983] using wordTrace_append hprefix tailTrace_2237983
  have hstable : (prefixWord ++ tailWord_2237983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237983).length < 2 ^ (prefixWord ++ tailWord_2237983).sum := by decide
  have hdescent : baseEnd_2237983 < baseStart_2237983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2237985 : List Nat := [1, 2, 3, 2, 2, 2, 4, 2, 4]
def baseStart_2237985 : Nat := 118140960795 + 2237985 * 2 ^ 59
def prefixEnd_2237985 : Nat := 4983230072969 + 3 ^ 40 * 2237985 * 2
def baseEnd_2237985 : Nat := 255369333900562579354489

theorem tailTrace_2237985 : CollatzResearch.WordTrace tailWord_2237985 prefixEnd_2237985 255369333900562579354489 := by
  unfold tailWord_2237985
  simp only [CollatzResearch.WordTrace]
  refine ⟨81626018797170037253227409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54417345864780024835484939 81626018797170037253227409)
  ·
    refine ⟨61219514097877527939920557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81626018797170037253227409 61219514097877527939920557)
    ·
      refine ⟨22957317786704072977470209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61219514097877527939920557 22957317786704072977470209)
      ·
        refine ⟨17217988340028054733102657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22957317786704072977470209 17217988340028054733102657)
        ·
          refine ⟨12913491255021041049826993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17217988340028054733102657 12913491255021041049826993)
          ·
            refine ⟨9685118441265780787370245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12913491255021041049826993 9685118441265780787370245)
            ·
              refine ⟨1815959707737333897631921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9685118441265780787370245 1815959707737333897631921)
              ·
                refine ⟨1361969780803000423223941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1815959707737333897631921 1361969780803000423223941)
                ·
                  refine ⟨255369333900562579354489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1361969780803000423223941 255369333900562579354489)
                  ·
                    rfl

theorem cell22_2237985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 4].length) (baseStart_2237985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2237985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2237985 prefixEnd_2237985 := by exact prefixLift 2237985
  have htrace : WordTrace (prefixWord ++ tailWord_2237985) baseStart_2237985 baseEnd_2237985 := by
    simpa [prefixWord, tailWord_2237985, baseEnd_2237985] using wordTrace_append hprefix tailTrace_2237985
  have hstable : (prefixWord ++ tailWord_2237985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2237985).length < 2 ^ (prefixWord ++ tailWord_2237985).sum := by decide
  have hdescent : baseEnd_2237985 < baseStart_2237985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2237985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238103 : List Nat := [1, 1, 3, 3, 2, 2, 3, 1, 6]
def baseStart_2238103 : Nat := 118140960795 + 2238103 * 2 ^ 59
def prefixEnd_2238103 : Nat := 4983230072969 + 3 ^ 40 * 2238103 * 2
def baseEnd_2238103 : Nat := 255382798504391587871035

theorem tailTrace_2238103 : CollatzResearch.WordTrace tailWord_2238103 prefixEnd_2238103 255382798504391587871035 := by
  unfold tailWord_2238103
  simp only [CollatzResearch.WordTrace]
  refine ⟨81630322610742543406022963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54420215073828362270681975 81630322610742543406022963)
  ·
    refine ⟨122445483916113815109034445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81630322610742543406022963 122445483916113815109034445)
    ·
      refine ⟨45917056468542680665887917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122445483916113815109034445 45917056468542680665887917)
      ·
        refine ⟨17218896175703505249707969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45917056468542680665887917 17218896175703505249707969)
        ·
          refine ⟨12914172131777628937280977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17218896175703505249707969 12914172131777628937280977)
          ·
            refine ⟨9685629098833221702960733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12914172131777628937280977 9685629098833221702960733)
            ·
              refine ⟨3632110912062458138610275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9685629098833221702960733 3632110912062458138610275)
              ·
                refine ⟨5448166368093687207915413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3632110912062458138610275 5448166368093687207915413)
                ·
                  refine ⟨255382798504391587871035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5448166368093687207915413 255382798504391587871035)
                  ·
                    rfl

theorem cell22_2238103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 6].length) (baseStart_2238103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238103 prefixEnd_2238103 := by exact prefixLift 2238103
  have htrace : WordTrace (prefixWord ++ tailWord_2238103) baseStart_2238103 baseEnd_2238103 := by
    simpa [prefixWord, tailWord_2238103, baseEnd_2238103] using wordTrace_append hprefix tailTrace_2238103
  have hstable : (prefixWord ++ tailWord_2238103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238103).length < 2 ^ (prefixWord ++ tailWord_2238103).sum := by decide
  have hdescent : baseEnd_2238103 < baseStart_2238103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238131 : List Nat := [1, 1, 1, 2, 3, 3, 1, 10]
def baseStart_2238131 : Nat := 118140960795 + 2238131 * 2 ^ 59
def prefixEnd_2238131 : Nat := 4983230072969 + 3 ^ 40 * 2238131 * 2
def baseEnd_2238131 : Nat := 85128664498376891545891

theorem tailTrace_2238131 : CollatzResearch.WordTrace tailWord_2238131 prefixEnd_2238131 85128664498376891545891 := by
  unfold tailWord_2238131
  simp only [CollatzResearch.WordTrace]
  refine ⟨81631343854641104188042247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54420895903094069458694831 81631343854641104188042247)
  ·
    refine ⟨122447015781961656282063371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81631343854641104188042247 122447015781961656282063371)
    ·
      refine ⟨183670523672942484423095057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122447015781961656282063371 183670523672942484423095057)
      ·
        refine ⟨137752892754706863317321293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183670523672942484423095057 137752892754706863317321293)
        ·
          refine ⟨51657334783015073743995485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137752892754706863317321293 51657334783015073743995485)
          ·
            refine ⟨19371500543630652653998307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51657334783015073743995485 19371500543630652653998307)
            ·
              refine ⟨29057250815445978980997461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19371500543630652653998307 29057250815445978980997461)
              ·
                refine ⟨85128664498376891545891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29057250815445978980997461 85128664498376891545891)
                ·
                  rfl

theorem cell22_2238131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 10].length) (baseStart_2238131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238131 prefixEnd_2238131 := by exact prefixLift 2238131
  have htrace : WordTrace (prefixWord ++ tailWord_2238131) baseStart_2238131 baseEnd_2238131 := by
    simpa [prefixWord, tailWord_2238131, baseEnd_2238131] using wordTrace_append hprefix tailTrace_2238131
  have hstable : (prefixWord ++ tailWord_2238131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238131).length < 2 ^ (prefixWord ++ tailWord_2238131).sum := by decide
  have hdescent : baseEnd_2238131 < baseStart_2238131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238154 : List Nat := [3, 1, 2, 1, 5, 2, 2, 2, 4]
def baseStart_2238154 : Nat := 118140960795 + 2238154 * 2 ^ 59
def prefixEnd_2238154 : Nat := 4983230072969 + 3 ^ 40 * 2238154 * 2
def baseEnd_2238154 : Nat := 255388617951809210195983

theorem tailTrace_2238154 : CollatzResearch.WordTrace tailWord_2238154 prefixEnd_2238154 255388617951809210195983 := by
  unfold tailWord_2238154
  simp only [CollatzResearch.WordTrace]
  refine ⟨20408045683389444779032379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54421455155705186077419677 20408045683389444779032379)
  ·
    refine ⟨30612068525084167168548569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20408045683389444779032379 30612068525084167168548569)
    ·
      refine ⟨22959051393813125376411427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30612068525084167168548569 22959051393813125376411427)
      ·
        refine ⟨34438577090719688064617141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22959051393813125376411427 34438577090719688064617141)
        ·
          refine ⟨3228616602254970756057857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34438577090719688064617141 3228616602254970756057857)
          ·
            refine ⟨2421462451691228067043393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3228616602254970756057857 2421462451691228067043393)
            ·
              refine ⟨1816096838768421050282545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2421462451691228067043393 1816096838768421050282545)
              ·
                refine ⟨1362072629076315787711909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1816096838768421050282545 1362072629076315787711909)
                ·
                  refine ⟨255388617951809210195983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1362072629076315787711909 255388617951809210195983)
                  ·
                    rfl

theorem cell22_2238154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_2238154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238154 prefixEnd_2238154 := by exact prefixLift 2238154
  have htrace : WordTrace (prefixWord ++ tailWord_2238154) baseStart_2238154 baseEnd_2238154 := by
    simpa [prefixWord, tailWord_2238154, baseEnd_2238154] using wordTrace_append hprefix tailTrace_2238154
  have hstable : (prefixWord ++ tailWord_2238154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238154).length < 2 ^ (prefixWord ++ tailWord_2238154).sum := by decide
  have hdescent : baseEnd_2238154 < baseStart_2238154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238180 : List Nat := [2, 3, 1, 1, 1, 3, 3, 2, 3, 3]
def baseStart_2238180 : Nat := 118140960795 + 2238180 * 2 ^ 59
def prefixEnd_2238180 : Nat := 4983230072969 + 3 ^ 40 * 2238180 * 2
def baseEnd_2238180 : Nat := 766174754186772229437869

theorem tailTrace_2238180 : CollatzResearch.WordTrace tailWord_2238180 prefixEnd_2238180 766174754186772229437869 := by
  unfold tailWord_2238180
  simp only [CollatzResearch.WordTrace]
  refine ⟨40816565515731792778287997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54422087354309057037717329 40816565515731792778287997)
  ·
    refine ⟨15306212068399422291857999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40816565515731792778287997 15306212068399422291857999)
    ·
      refine ⟨22959318102599133437786999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15306212068399422291857999 22959318102599133437786999)
      ·
        refine ⟨34438977153898700156680499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22959318102599133437786999 34438977153898700156680499)
        ·
          refine ⟨51658465730848050235020749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34438977153898700156680499 51658465730848050235020749)
          ·
            refine ⟨19371924649068018838132781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51658465730848050235020749 19371924649068018838132781)
            ·
              refine ⟨7264471743400507064299793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19371924649068018838132781 7264471743400507064299793)
              ·
                refine ⟨5448353807550380298224845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7264471743400507064299793 5448353807550380298224845)
                ·
                  refine ⟨2043132677831392611834317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5448353807550380298224845 2043132677831392611834317)
                  ·
                    refine ⟨766174754186772229437869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2043132677831392611834317 766174754186772229437869)
                    ·
                      rfl

theorem cell22_2238180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_2238180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238180 prefixEnd_2238180 := by exact prefixLift 2238180
  have htrace : WordTrace (prefixWord ++ tailWord_2238180) baseStart_2238180 baseEnd_2238180 := by
    simpa [prefixWord, tailWord_2238180, baseEnd_2238180] using wordTrace_append hprefix tailTrace_2238180
  have hstable : (prefixWord ++ tailWord_2238180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238180).length < 2 ^ (prefixWord ++ tailWord_2238180).sum := by decide
  have hdescent : baseEnd_2238180 < baseStart_2238180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238210 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 7]
def baseStart_2238210 : Nat := 118140960795 + 2238210 * 2 ^ 59
def prefixEnd_2238210 : Nat := 4983230072969 + 3 ^ 40 * 2238210 * 2
def baseEnd_2238210 : Nat := 255395007933287383729259

theorem tailTrace_2238210 : CollatzResearch.WordTrace tailWord_2238210 prefixEnd_2238210 255395007933287383729259 := by
  unfold tailWord_2238210
  simp only [CollatzResearch.WordTrace]
  refine ⟨20408556305338725170042021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54422816814236600453445389 20408556305338725170042021)
  ·
    refine ⟨3826604307251010969382879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20408556305338725170042021 3826604307251010969382879)
    ·
      refine ⟨5739906460876516454074319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3826604307251010969382879 5739906460876516454074319)
      ·
        refine ⟨8609859691314774681111479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5739906460876516454074319 8609859691314774681111479)
        ·
          refine ⟨12914789536972162021667219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8609859691314774681111479 12914789536972162021667219)
          ·
            refine ⟨19372184305458243032500829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12914789536972162021667219 19372184305458243032500829)
            ·
              refine ⟨7264569114546841137187811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19372184305458243032500829 7264569114546841137187811)
              ·
                refine ⟨10896853671820261705781717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7264569114546841137187811 10896853671820261705781717)
                ·
                  refine ⟨255395007933287383729259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10896853671820261705781717 255395007933287383729259)
                  ·
                    rfl

theorem cell22_2238210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_2238210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238210 prefixEnd_2238210 := by exact prefixLift 2238210
  have htrace : WordTrace (prefixWord ++ tailWord_2238210) baseStart_2238210 baseEnd_2238210 := by
    simpa [prefixWord, tailWord_2238210, baseEnd_2238210] using wordTrace_append hprefix tailTrace_2238210
  have hstable : (prefixWord ++ tailWord_2238210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238210).length < 2 ^ (prefixWord ++ tailWord_2238210).sum := by decide
  have hdescent : baseEnd_2238210 < baseStart_2238210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238223 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 3, 4]
def baseStart_2238223 : Nat := 118140960795 + 2238223 * 2 ^ 59
def prefixEnd_2238223 : Nat := 4983230072969 + 3 ^ 40 * 2238223 * 2
def baseEnd_2238223 : Nat := 766189473965534450612737

theorem tailTrace_2238223 : CollatzResearch.WordTrace tailWord_2238223 prefixEnd_2238223 766189473965534450612737 := by
  unfold tailWord_2238223
  simp only [CollatzResearch.WordTrace]
  refine ⟨81634699370307803900391323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54423132913538535933594215 81634699370307803900391323)
  ·
    refine ⟨122452049055461705850586985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81634699370307803900391323 122452049055461705850586985)
    ·
      refine ⟨91839036791596279387940239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122452049055461705850586985 91839036791596279387940239)
      ·
        refine ⟨137758555187394419081910359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91839036791596279387940239 137758555187394419081910359)
        ·
          refine ⟨206637832781091628622865539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137758555187394419081910359 206637832781091628622865539)
          ·
            refine ⟨309956749171637442934298309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206637832781091628622865539 309956749171637442934298309)
            ·
              refine ⟨58116890469682020550180933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 309956749171637442934298309 58116890469682020550180933)
              ·
                refine ⟨10896916963065378853158925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58116890469682020550180933 10896916963065378853158925)
                ·
                  refine ⟨4086343861149517069934597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10896916963065378853158925 4086343861149517069934597)
                  ·
                    refine ⟨766189473965534450612737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4086343861149517069934597 766189473965534450612737)
                    ·
                      rfl

theorem cell22_2238223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_2238223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238223 prefixEnd_2238223 := by exact prefixLift 2238223
  have htrace : WordTrace (prefixWord ++ tailWord_2238223) baseStart_2238223 baseEnd_2238223 := by
    simpa [prefixWord, tailWord_2238223, baseEnd_2238223] using wordTrace_append hprefix tailTrace_2238223
  have hstable : (prefixWord ++ tailWord_2238223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238223).length < 2 ^ (prefixWord ++ tailWord_2238223).sum := by decide
  have hdescent : baseEnd_2238223 < baseStart_2238223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238313 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 4, 6]
def baseStart_2238313 : Nat := 118140960795 + 2238313 * 2 ^ 59
def prefixEnd_2238313 : Nat := 4983230072969 + 3 ^ 40 * 2238313 * 2
def baseEnd_2238313 : Nat := 766220282804804215862461

theorem tailTrace_2238313 : CollatzResearch.WordTrace tailWord_2238313 prefixEnd_2238313 766220282804804215862461 := by
  unfold tailWord_2238313
  simp only [CollatzResearch.WordTrace]
  refine ⟨81637981939981749271167593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54425321293321166180778395 81637981939981749271167593)
  ·
    refine ⟨61228486454986311953375695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81637981939981749271167593 61228486454986311953375695)
    ·
      refine ⟨91842729682479467930063543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61228486454986311953375695 91842729682479467930063543)
      ·
        refine ⟨137764094523719201895095315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91842729682479467930063543 137764094523719201895095315)
        ·
          refine ⟨206646141785578802842642973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137764094523719201895095315 206646141785578802842642973)
          ·
            refine ⟨77492303169592051065991115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206646141785578802842642973 77492303169592051065991115)
            ·
              refine ⟨116238454754388076598986673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77492303169592051065991115 116238454754388076598986673)
              ·
                refine ⟨87178841065791057449240005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116238454754388076598986673 87178841065791057449240005)
                ·
                  refine ⟨16346032699835823271732501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87178841065791057449240005 16346032699835823271732501)
                  ·
                    refine ⟨766220282804804215862461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16346032699835823271732501 766220282804804215862461)
                    ·
                      rfl

theorem cell22_2238313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_2238313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238313 prefixEnd_2238313 := by exact prefixLift 2238313
  have htrace : WordTrace (prefixWord ++ tailWord_2238313) baseStart_2238313 baseEnd_2238313 := by
    simpa [prefixWord, tailWord_2238313, baseEnd_2238313] using wordTrace_append hprefix tailTrace_2238313
  have hstable : (prefixWord ++ tailWord_2238313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238313).length < 2 ^ (prefixWord ++ tailWord_2238313).sum := by decide
  have hdescent : baseEnd_2238313 < baseStart_2238313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238328 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 11]
def baseStart_2238328 : Nat := 118140960795 + 2238328 * 2 ^ 59
def prefixEnd_2238328 : Nat := 4983230072969 + 3 ^ 40 * 2238328 * 2
def baseEnd_2238328 : Nat := 255408472537116392245805

theorem tailTrace_2238328 : CollatzResearch.WordTrace tailWord_2238328 prefixEnd_2238328 255408472537116392245805 := by
  unfold tailWord_2238328
  simp only [CollatzResearch.WordTrace]
  refine ⟨40819264517463703416481819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54425686023284937888642425 40819264517463703416481819)
  ·
    refine ⟨61228896776195555124722729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40819264517463703416481819 61228896776195555124722729)
    ·
      refine ⟨45921672582146666343542047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61228896776195555124722729 45921672582146666343542047)
      ·
        refine ⟨68882508873219999515313071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45921672582146666343542047 68882508873219999515313071)
        ·
          refine ⟨103323763309829999272969607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68882508873219999515313071 103323763309829999272969607)
          ·
            refine ⟨154985644964744998909454411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103323763309829999272969607 154985644964744998909454411)
            ·
              refine ⟨232478467447117498364181617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154985644964744998909454411 232478467447117498364181617)
              ·
                refine ⟨174358850585338123773136213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232478467447117498364181617 174358850585338123773136213)
                ·
                  refine ⟨255408472537116392245805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 174358850585338123773136213 255408472537116392245805)
                  ·
                    rfl

theorem cell22_2238328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 11].length) (baseStart_2238328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238328 prefixEnd_2238328 := by exact prefixLift 2238328
  have htrace : WordTrace (prefixWord ++ tailWord_2238328) baseStart_2238328 baseEnd_2238328 := by
    simpa [prefixWord, tailWord_2238328, baseEnd_2238328] using wordTrace_append hprefix tailTrace_2238328
  have hstable : (prefixWord ++ tailWord_2238328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238328).length < 2 ^ (prefixWord ++ tailWord_2238328).sum := by decide
  have hdescent : baseEnd_2238328 < baseStart_2238328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238334 : List Nat := [4, 2, 3, 1, 1, 3, 1, 7]
def baseStart_2238334 : Nat := 118140960795 + 2238334 * 2 ^ 59
def prefixEnd_2238334 : Nat := 4983230072969 + 3 ^ 40 * 2238334 * 2
def baseEnd_2238334 : Nat := 85136385725996351231933

theorem tailTrace_2238334 : CollatzResearch.WordTrace tailWord_2238334 prefixEnd_2238334 85136385725996351231933 := by
  unfold tailWord_2238334
  simp only [CollatzResearch.WordTrace]
  refine ⟨10204843484113208732210257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54425831915270446571788037 10204843484113208732210257)
  ·
    refine ⟨7653632613084906549157693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10204843484113208732210257 7653632613084906549157693)
    ·
      refine ⟨2870112229906839955934135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7653632613084906549157693 2870112229906839955934135)
      ·
        refine ⟨4305168344860259933901203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2870112229906839955934135 4305168344860259933901203)
        ·
          refine ⟨6457752517290389900851805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4305168344860259933901203 6457752517290389900851805)
          ·
            refine ⟨2421657193983896212819427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6457752517290389900851805 2421657193983896212819427)
            ·
              refine ⟨3632485790975844319229141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2421657193983896212819427 3632485790975844319229141)
              ·
                refine ⟨85136385725996351231933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3632485790975844319229141 85136385725996351231933)
                ·
                  rfl

theorem cell22_2238334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_2238334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238334 prefixEnd_2238334 := by exact prefixLift 2238334
  have htrace : WordTrace (prefixWord ++ tailWord_2238334) baseStart_2238334 baseEnd_2238334 := by
    simpa [prefixWord, tailWord_2238334, baseEnd_2238334] using wordTrace_append hprefix tailTrace_2238334
  have hstable : (prefixWord ++ tailWord_2238334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238334).length < 2 ^ (prefixWord ++ tailWord_2238334).sum := by decide
  have hdescent : baseEnd_2238334 < baseStart_2238334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238345 : List Nat := [1, 2, 1, 1, 5, 1, 1, 5, 5]
def baseStart_2238345 : Nat := 118140960795 + 2238345 * 2 ^ 59
def prefixEnd_2238345 : Nat := 4983230072969 + 3 ^ 40 * 2238345 * 2
def baseEnd_2238345 : Nat := 255410412352922266354121

theorem tailTrace_2238345 : CollatzResearch.WordTrace tailWord_2238345 prefixEnd_2238345 255410412352922266354121 := by
  unfold tailWord_2238345
  simp only [CollatzResearch.WordTrace]
  refine ⟨81639149075865818736332489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54426099383910545824221659 81639149075865818736332489)
  ·
    refine ⟨61229361806899364052249367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81639149075865818736332489 61229361806899364052249367)
    ·
      refine ⟨91844042710349046078374051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61229361806899364052249367 91844042710349046078374051)
      ·
        refine ⟨137766064065523569117561077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91844042710349046078374051 137766064065523569117561077)
        ·
          refine ⟨12915568506142834604771351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 137766064065523569117561077 12915568506142834604771351)
          ·
            refine ⟨19373352759214251907157027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12915568506142834604771351 19373352759214251907157027)
            ·
              refine ⟨29060029138821377860735541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19373352759214251907157027 29060029138821377860735541)
              ·
                refine ⟨2724377731764504174443957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29060029138821377860735541 2724377731764504174443957)
                ·
                  refine ⟨255410412352922266354121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2724377731764504174443957 255410412352922266354121)
                  ·
                    rfl

theorem cell22_2238345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 5].length) (baseStart_2238345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238345 prefixEnd_2238345 := by exact prefixLift 2238345
  have htrace : WordTrace (prefixWord ++ tailWord_2238345) baseStart_2238345 baseEnd_2238345 := by
    simpa [prefixWord, tailWord_2238345, baseEnd_2238345] using wordTrace_append hprefix tailTrace_2238345
  have hstable : (prefixWord ++ tailWord_2238345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238345).length < 2 ^ (prefixWord ++ tailWord_2238345).sum := by decide
  have hdescent : baseEnd_2238345 < baseStart_2238345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238396 : List Nat := [2, 2, 2, 5, 1, 1, 3, 1, 5]
def baseStart_2238396 : Nat := 118140960795 + 2238396 * 2 ^ 59
def prefixEnd_2238396 : Nat := 4983230072969 + 3 ^ 40 * 2238396 * 2
def baseEnd_2238396 : Nat := 255416231800339888679069

theorem tailTrace_2238396 : CollatzResearch.WordTrace tailWord_2238396 prefixEnd_2238396 255416231800339888679069 := by
  unfold tailWord_2238396
  simp only [CollatzResearch.WordTrace]
  refine ⟨40820504599340527223219521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54427339465787369630959361 40820504599340527223219521)
  ·
    refine ⟨30615378449505395417414641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40820504599340527223219521 30615378449505395417414641)
    ·
      refine ⟨22961533837129046563060981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30615378449505395417414641 22961533837129046563060981)
      ·
        refine ⟨2152643797230848115286967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22961533837129046563060981 2152643797230848115286967)
        ·
          refine ⟨3228965695846272172930451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2152643797230848115286967 3228965695846272172930451)
          ·
            refine ⟨4843448543769408259395677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3228965695846272172930451 4843448543769408259395677)
            ·
              refine ⟨1816293203913528097273379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4843448543769408259395677 1816293203913528097273379)
              ·
                refine ⟨2724439805870292145910069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1816293203913528097273379 2724439805870292145910069)
                ·
                  refine ⟨255416231800339888679069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2724439805870292145910069 255416231800339888679069)
                  ·
                    rfl

theorem cell22_2238396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_2238396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238396 prefixEnd_2238396 := by exact prefixLift 2238396
  have htrace : WordTrace (prefixWord ++ tailWord_2238396) baseStart_2238396 baseEnd_2238396 := by
    simpa [prefixWord, tailWord_2238396, baseEnd_2238396] using wordTrace_append hprefix tailTrace_2238396
  have hstable : (prefixWord ++ tailWord_2238396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238396).length < 2 ^ (prefixWord ++ tailWord_2238396).sum := by decide
  have hdescent : baseEnd_2238396 < baseStart_2238396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238405 : List Nat := [1, 3, 1, 1, 1, 1, 1, 7, 1, 5]
def baseStart_2238405 : Nat := 118140960795 + 2238405 * 2 ^ 59
def prefixEnd_2238405 : Nat := 4983230072969 + 3 ^ 40 * 2238405 * 2
def baseEnd_2238405 : Nat := 766251776284946642562179

theorem tailTrace_2238405 : CollatzResearch.WordTrace tailWord_2238405 prefixEnd_2238405 766251776284946642562179 := by
  unfold tailWord_2238405
  simp only [CollatzResearch.WordTrace]
  refine ⟨81641337455648448983516669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54427558303765632655677779 81641337455648448983516669)
  ·
    refine ⟨30615501545868168368818751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81641337455648448983516669 30615501545868168368818751)
    ·
      refine ⟨45923252318802252553228127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30615501545868168368818751 45923252318802252553228127)
      ·
        refine ⟨68884878478203378829842191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45923252318802252553228127 68884878478203378829842191)
        ·
          refine ⟨103327317717305068244763287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68884878478203378829842191 103327317717305068244763287)
          ·
            refine ⟨154990976575957602367144931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103327317717305068244763287 154990976575957602367144931)
            ·
              refine ⟨232486464863936403550717397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154990976575957602367144931 232486464863936403550717397)
              ·
                refine ⟨5448901520248509458219939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 232486464863936403550717397 5448901520248509458219939)
                ·
                  refine ⟨8173352280372764187329909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5448901520248509458219939 8173352280372764187329909)
                  ·
                    refine ⟨766251776284946642562179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8173352280372764187329909 766251776284946642562179)
                    ·
                      rfl

theorem cell22_2238405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_2238405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238405 prefixEnd_2238405 := by exact prefixLift 2238405
  have htrace : WordTrace (prefixWord ++ tailWord_2238405) baseStart_2238405 baseEnd_2238405 := by
    simpa [prefixWord, tailWord_2238405, baseEnd_2238405] using wordTrace_append hprefix tailTrace_2238405
  have hstable : (prefixWord ++ tailWord_2238405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238405).length < 2 ^ (prefixWord ++ tailWord_2238405).sum := by decide
  have hdescent : baseEnd_2238405 < baseStart_2238405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238435 : List Nat := [1, 1, 1, 6, 1, 2, 10]
def baseStart_2238435 : Nat := 118140960795 + 2238435 * 2 ^ 59
def prefixEnd_2238435 : Nat := 4983230072969 + 3 ^ 40 * 2238435 * 2
def baseEnd_2238435 : Nat := 28380075774001354233781

theorem tailTrace_2238435 : CollatzResearch.WordTrace tailWord_2238435 prefixEnd_2238435 28380075774001354233781 := by
  unfold tailWord_2238435
  simp only [CollatzResearch.WordTrace]
  refine ⟨81642431645539764107108759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54428287763693176071405839 81642431645539764107108759)
  ·
    refine ⟨122463647468309646160663139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81642431645539764107108759 122463647468309646160663139)
    ·
      refine ⟨183695471202464469240994709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122463647468309646160663139 183695471202464469240994709)
      ·
        refine ⟨8610725212615521995671627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 183695471202464469240994709 8610725212615521995671627)
        ·
          refine ⟨12916087818923282993507441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8610725212615521995671627 12916087818923282993507441)
          ·
            refine ⟨9687065864192462245130581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12916087818923282993507441 9687065864192462245130581)
            ·
              refine ⟨28380075774001354233781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9687065864192462245130581 28380075774001354233781)
              ·
                rfl

theorem cell22_2238435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 10].length) (baseStart_2238435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238435 prefixEnd_2238435 := by exact prefixLift 2238435
  have htrace : WordTrace (prefixWord ++ tailWord_2238435) baseStart_2238435 baseEnd_2238435 := by
    simpa [prefixWord, tailWord_2238435, baseEnd_2238435] using wordTrace_append hprefix tailTrace_2238435
  have hstable : (prefixWord ++ tailWord_2238435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238435).length < 2 ^ (prefixWord ++ tailWord_2238435).sum := by decide
  have hdescent : baseEnd_2238435 < baseStart_2238435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238467 : List Nat := [1, 1, 1, 3, 2, 1, 1, 6, 3, 3]
def baseStart_2238467 : Nat := 118140960795 + 2238467 * 2 ^ 59
def prefixEnd_2238467 : Nat := 4983230072969 + 3 ^ 40 * 2238467 * 2
def baseEnd_2238467 : Nat := 766273000151999147511989

theorem tailTrace_2238467 : CollatzResearch.WordTrace tailWord_2238467 prefixEnd_2238467 766273000151999147511989 := by
  unfold tailWord_2238467
  simp only [CollatzResearch.WordTrace]
  refine ⟨81643598781423833572273655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54429065854282555714849103 81643598781423833572273655)
  ·
    refine ⟨122465398172135750358410483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81643598781423833572273655 122465398172135750358410483)
    ·
      refine ⟨183698097258203625537615725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122465398172135750358410483 183698097258203625537615725)
      ·
        refine ⟨68886786471826359576605897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183698097258203625537615725 68886786471826359576605897)
        ·
          refine ⟨51665089853869769682454423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68886786471826359576605897 51665089853869769682454423)
          ·
            refine ⟨77497634780804654523681635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51665089853869769682454423 77497634780804654523681635)
            ·
              refine ⟨116246452171206981785522453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77497634780804654523681635 116246452171206981785522453)
              ·
                refine ⟨5449052445525327271196365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 116246452171206981785522453 5449052445525327271196365)
                ·
                  refine ⟨2043394667071997726698637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5449052445525327271196365 2043394667071997726698637)
                  ·
                    refine ⟨766273000151999147511989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2043394667071997726698637 766273000151999147511989)
                    ·
                      rfl

theorem cell22_2238467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 3].length) (baseStart_2238467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238467 prefixEnd_2238467 := by exact prefixLift 2238467
  have htrace : WordTrace (prefixWord ++ tailWord_2238467) baseStart_2238467 baseEnd_2238467 := by
    simpa [prefixWord, tailWord_2238467, baseEnd_2238467] using wordTrace_append hprefix tailTrace_2238467
  have hstable : (prefixWord ++ tailWord_2238467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238467).length < 2 ^ (prefixWord ++ tailWord_2238467).sum := by decide
  have hdescent : baseEnd_2238467 < baseStart_2238467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238501 : List Nat := [1, 3, 1, 2, 2, 4, 1, 4, 1, 3]
def baseStart_2238501 : Nat := 118140960795 + 2238501 * 2 ^ 59
def prefixEnd_2238501 : Nat := 4983230072969 + 3 ^ 40 * 2238501 * 2
def baseEnd_2238501 : Nat := 766284639046834392161885

theorem tailTrace_2238501 : CollatzResearch.WordTrace tailWord_2238501 prefixEnd_2238501 766284639046834392161885 := by
  unfold tailWord_2238501
  simp only [CollatzResearch.WordTrace]
  refine ⟨81644838863300657379011357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54429892575533771586007571 81644838863300657379011357)
  ·
    refine ⟨30616814573737746517129259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81644838863300657379011357 30616814573737746517129259)
    ·
      refine ⟨45925221860606619775693889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30616814573737746517129259 45925221860606619775693889)
      ·
        refine ⟨34443916395454964831770417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45925221860606619775693889 34443916395454964831770417)
        ·
          refine ⟨25832937296591223623827813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34443916395454964831770417 25832937296591223623827813)
          ·
            refine ⟨4843675743110854429467715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25832937296591223623827813 4843675743110854429467715)
            ·
              refine ⟨7265513614666281644201573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4843675743110854429467715 7265513614666281644201573)
              ·
                refine ⟨1362283802749927808287795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7265513614666281644201573 1362283802749927808287795)
                ·
                  refine ⟨2043425704124891712431693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1362283802749927808287795 2043425704124891712431693)
                  ·
                    refine ⟨766284639046834392161885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2043425704124891712431693 766284639046834392161885)
                    ·
                      rfl

theorem cell22_2238501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 1, 3].length) (baseStart_2238501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238501 prefixEnd_2238501 := by exact prefixLift 2238501
  have htrace : WordTrace (prefixWord ++ tailWord_2238501) baseStart_2238501 baseEnd_2238501 := by
    simpa [prefixWord, tailWord_2238501, baseEnd_2238501] using wordTrace_append hprefix tailTrace_2238501
  have hstable : (prefixWord ++ tailWord_2238501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238501).length < 2 ^ (prefixWord ++ tailWord_2238501).sum := by decide
  have hdescent : baseEnd_2238501 < baseStart_2238501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238512 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 2, 5]
def baseStart_2238512 : Nat := 118140960795 + 2238512 * 2 ^ 59
def prefixEnd_2238512 : Nat := 4983230072969 + 3 ^ 40 * 2238512 * 2
def baseEnd_2238512 : Nat := 766288404571634030136851

theorem tailTrace_2238512 : CollatzResearch.WordTrace tailWord_2238512 prefixEnd_2238512 766288404571634030136851 := by
  unfold tailWord_2238512
  simp only [CollatzResearch.WordTrace]
  refine ⟨40822620033130403128830895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54430160044173870838441193 40822620033130403128830895)
  ·
    refine ⟨61233930049695604693246343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40822620033130403128830895 61233930049695604693246343)
    ·
      refine ⟨91850895074543407039869515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61233930049695604693246343 91850895074543407039869515)
      ·
        refine ⟨137776342611815110559804273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91850895074543407039869515 137776342611815110559804273)
        ·
          refine ⟨103332256958861332919853205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137776342611815110559804273 103332256958861332919853205)
          ·
            refine ⟨4843699544946624980618119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103332256958861332919853205 4843699544946624980618119)
            ·
              refine ⟨7265549317419937470927179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4843699544946624980618119 7265549317419937470927179)
              ·
                refine ⟨10898323976129906206390769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7265549317419937470927179 10898323976129906206390769)
                ·
                  refine ⟨8173742982097429654793077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10898323976129906206390769 8173742982097429654793077)
                  ·
                    refine ⟨766288404571634030136851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8173742982097429654793077 766288404571634030136851)
                    ·
                      rfl

theorem cell22_2238512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_2238512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238512 prefixEnd_2238512 := by exact prefixLift 2238512
  have htrace : WordTrace (prefixWord ++ tailWord_2238512) baseStart_2238512 baseEnd_2238512 := by
    simpa [prefixWord, tailWord_2238512, baseEnd_2238512] using wordTrace_append hprefix tailTrace_2238512
  have hstable : (prefixWord ++ tailWord_2238512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238512).length < 2 ^ (prefixWord ++ tailWord_2238512).sum := by decide
  have hdescent : baseEnd_2238512 < baseStart_2238512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238527 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 3, 4]
def baseStart_2238527 : Nat := 118140960795 + 2238527 * 2 ^ 59
def prefixEnd_2238527 : Nat := 4983230072969 + 3 ^ 40 * 2238527 * 2
def baseEnd_2238527 : Nat := 766293539378178991011805

theorem tailTrace_2238527 : CollatzResearch.WordTrace tailWord_2238527 prefixEnd_2238527 766293539378178991011805 := by
  unfold tailWord_2238527
  simp only [CollatzResearch.WordTrace]
  refine ⟨81645787161206463819457835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54430524774137642546305223 81645787161206463819457835)
  ·
    refine ⟨122468680741809695729186753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81645787161206463819457835 122468680741809695729186753)
    ·
      refine ⟨91851510556357271796890065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122468680741809695729186753 91851510556357271796890065)
      ·
        refine ⟨68888632917267953847667549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91851510556357271796890065 68888632917267953847667549)
        ·
          refine ⟨25833237343975482692875331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68888632917267953847667549 25833237343975482692875331)
          ·
            refine ⟨38749856015963224039312997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25833237343975482692875331 38749856015963224039312997)
            ·
              refine ⟨7265598002993104507371187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38749856015963224039312997 7265598002993104507371187)
              ·
                refine ⟨10898397004489656761056781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7265598002993104507371187 10898397004489656761056781)
                ·
                  refine ⟨4086898876683621285396293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10898397004489656761056781 4086898876683621285396293)
                  ·
                    refine ⟨766293539378178991011805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4086898876683621285396293 766293539378178991011805)
                    ·
                      rfl

theorem cell22_2238527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_2238527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238527 prefixEnd_2238527 := by exact prefixLift 2238527
  have htrace : WordTrace (prefixWord ++ tailWord_2238527) baseStart_2238527 baseEnd_2238527 := by
    simpa [prefixWord, tailWord_2238527, baseEnd_2238527] using wordTrace_append hprefix tailTrace_2238527
  have hstable : (prefixWord ++ tailWord_2238527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238527).length < 2 ^ (prefixWord ++ tailWord_2238527).sum := by decide
  have hdescent : baseEnd_2238527 < baseStart_2238527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238572 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 1, 6]
def baseStart_2238572 : Nat := 118140960795 + 2238572 * 2 ^ 59
def prefixEnd_2238572 : Nat := 4983230072969 + 3 ^ 40 * 2238572 * 2
def baseEnd_2238572 : Nat := 766308943797813873636667

theorem tailTrace_2238572 : CollatzResearch.WordTrace tailWord_2238572 prefixEnd_2238572 766308943797813873636667 := by
  unfold tailWord_2238572
  simp only [CollatzResearch.WordTrace]
  refine ⟨40823714223021718252422985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54431618964028957669897313 40823714223021718252422985)
  ·
    refine ⟨30617785667266288689317239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40823714223021718252422985 30617785667266288689317239)
    ·
      refine ⟨45926678500899433033975859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30617785667266288689317239 45926678500899433033975859)
      ·
        refine ⟨68890017751349149550963789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45926678500899433033975859 68890017751349149550963789)
        ·
          refine ⟨25833756656755931081611421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68890017751349149550963789 25833756656755931081611421)
          ·
            refine ⟨9687658746283474155604283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25833756656755931081611421 9687658746283474155604283)
            ·
              refine ⟨14531488119425211233406425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9687658746283474155604283 14531488119425211233406425)
              ·
                refine ⟨10898616089568908425054819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14531488119425211233406425 10898616089568908425054819)
                ·
                  refine ⟨16347924134353362637582229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10898616089568908425054819 16347924134353362637582229)
                  ·
                    refine ⟨766308943797813873636667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16347924134353362637582229 766308943797813873636667)
                    ·
                      rfl

theorem cell22_2238572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_2238572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238572 prefixEnd_2238572 := by exact prefixLift 2238572
  have htrace : WordTrace (prefixWord ++ tailWord_2238572) baseStart_2238572 baseEnd_2238572 := by
    simpa [prefixWord, tailWord_2238572, baseEnd_2238572] using wordTrace_append hprefix tailTrace_2238572
  have hstable : (prefixWord ++ tailWord_2238572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238572).length < 2 ^ (prefixWord ++ tailWord_2238572).sum := by decide
  have hdescent : baseEnd_2238572 < baseStart_2238572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238593 : List Nat := [1, 2, 4, 2, 3, 2, 1, 3, 4]
def baseStart_2238593 : Nat := 118140960795 + 2238593 * 2 ^ 59
def prefixEnd_2238593 : Nat := 4983230072969 + 3 ^ 40 * 2238593 * 2
def baseEnd_2238593 : Nat := 255438710842325606287201

theorem tailTrace_2238593 : CollatzResearch.WordTrace tailWord_2238593 prefixEnd_2238593 255438710842325606287201 := by
  unfold tailWord_2238593
  simp only [CollatzResearch.WordTrace]
  refine ⟨81648194378967357091360433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54432129585978238060906955 81648194378967357091360433)
  ·
    refine ⟨61236145784225517818520325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81648194378967357091360433 61236145784225517818520325)
    ·
      refine ⟨11481777334542284590972561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61236145784225517818520325 11481777334542284590972561)
      ·
        refine ⟨8611333000906713443229421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11481777334542284590972561 8611333000906713443229421)
        ·
          refine ⟨3229249875340017541211033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8611333000906713443229421 3229249875340017541211033)
          ·
            refine ⟨2421937406505013155908275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3229249875340017541211033 2421937406505013155908275)
            ·
              refine ⟨3632906109757519733862413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2421937406505013155908275 3632906109757519733862413)
              ·
                refine ⟨1362339791159069900198405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3632906109757519733862413 1362339791159069900198405)
                ·
                  refine ⟨255438710842325606287201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1362339791159069900198405 255438710842325606287201)
                  ·
                    rfl

theorem cell22_2238593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 4].length) (baseStart_2238593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238593 prefixEnd_2238593 := by exact prefixLift 2238593
  have htrace : WordTrace (prefixWord ++ tailWord_2238593) baseStart_2238593 baseEnd_2238593 := by
    simpa [prefixWord, tailWord_2238593, baseEnd_2238593] using wordTrace_append hprefix tailTrace_2238593
  have hstable : (prefixWord ++ tailWord_2238593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238593).length < 2 ^ (prefixWord ++ tailWord_2238593).sum := by decide
  have hdescent : baseEnd_2238593 < baseStart_2238593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238606 : List Nat := [4, 1, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_2238606 : Nat := 118140960795 + 2238606 * 2 ^ 59
def prefixEnd_2238606 : Nat := 4983230072969 + 3 ^ 40 * 2238606 * 2
def baseEnd_2238606 : Nat := 766320582692649118286563

theorem tailTrace_2238606 : CollatzResearch.WordTrace tailWord_2238606 prefixEnd_2238606 766320582692649118286563 := by
  unfold tailWord_2238606
  simp only [CollatzResearch.WordTrace]
  refine ⟨10206083565990032538947959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54432445685280173541055781 10206083565990032538947959)
  ·
    refine ⟨15309125348985048808421939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10206083565990032538947959 15309125348985048808421939)
    ·
      refine ⟨22963688023477573212632909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15309125348985048808421939 22963688023477573212632909)
      ·
        refine ⟨8611383008804089954737341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22963688023477573212632909 8611383008804089954737341)
        ·
          refine ⟨3229268628301533733026503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8611383008804089954737341 3229268628301533733026503)
          ·
            refine ⟨4843902942452300599539755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3229268628301533733026503 4843902942452300599539755)
            ·
              refine ⟨7265854413678450899309633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4843902942452300599539755 7265854413678450899309633)
              ·
                refine ⟨5449390810258838174482225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7265854413678450899309633 5449390810258838174482225)
                ·
                  refine ⟨4087043107694128630861669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5449390810258838174482225 4087043107694128630861669)
                  ·
                    refine ⟨766320582692649118286563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4087043107694128630861669 766320582692649118286563)
                    ·
                      rfl

theorem cell22_2238606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_2238606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238606 prefixEnd_2238606 := by exact prefixLift 2238606
  have htrace : WordTrace (prefixWord ++ tailWord_2238606) baseStart_2238606 baseEnd_2238606 := by
    simpa [prefixWord, tailWord_2238606, baseEnd_2238606] using wordTrace_append hprefix tailTrace_2238606
  have hstable : (prefixWord ++ tailWord_2238606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238606).length < 2 ^ (prefixWord ++ tailWord_2238606).sum := by decide
  have hdescent : baseEnd_2238606 < baseStart_2238606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238670 : List Nat := [4, 1, 1, 1, 4, 1, 4, 2, 1, 3]
def baseStart_2238670 : Nat := 118140960795 + 2238670 * 2 ^ 59
def prefixEnd_2238670 : Nat := 4983230072969 + 3 ^ 40 * 2238670 * 2
def baseEnd_2238670 : Nat := 766342491200574284686367

theorem tailTrace_2238670 : CollatzResearch.WordTrace tailWord_2238670 prefixEnd_2238670 766342491200574284686367 := by
  unfold tailWord_2238670
  simp only [CollatzResearch.WordTrace]
  refine ⟨10206375349961049905239183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54434001866458932827942309 10206375349961049905239183)
  ·
    refine ⟨15309563024941574857858775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10206375349961049905239183 15309563024941574857858775)
    ·
      refine ⟨22964344537412362286788163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15309563024941574857858775 22964344537412362286788163)
      ·
        refine ⟨34446516806118543430182245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22964344537412362286788163 34446516806118543430182245)
        ·
          refine ⟨6458721901147226893159171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34446516806118543430182245 6458721901147226893159171)
          ·
            refine ⟨9688082851720840339738757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6458721901147226893159171 9688082851720840339738757)
            ·
              refine ⟨1816515534697657563701017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9688082851720840339738757 1816515534697657563701017)
              ·
                refine ⟨1362386651023243172775763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1816515534697657563701017 1362386651023243172775763)
                ·
                  refine ⟨2043579976534864759163645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1362386651023243172775763 2043579976534864759163645)
                  ·
                    refine ⟨766342491200574284686367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2043579976534864759163645 766342491200574284686367)
                    ·
                      rfl

theorem cell22_2238670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_2238670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238670 prefixEnd_2238670 := by exact prefixLift 2238670
  have htrace : WordTrace (prefixWord ++ tailWord_2238670) baseStart_2238670 baseEnd_2238670 := by
    simpa [prefixWord, tailWord_2238670, baseEnd_2238670] using wordTrace_append hprefix tailTrace_2238670
  have hstable : (prefixWord ++ tailWord_2238670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238670).length < 2 ^ (prefixWord ++ tailWord_2238670).sum := by decide
  have hdescent : baseEnd_2238670 < baseStart_2238670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238756 : List Nat := [2, 3, 1, 3, 1, 2, 4, 6]
def baseStart_2238756 : Nat := 118140960795 + 2238756 * 2 ^ 59
def prefixEnd_2238756 : Nat := 4983230072969 + 3 ^ 40 * 2238756 * 2
def baseEnd_2238756 : Nat := 85152436750899858559567

theorem tailTrace_2238756 : CollatzResearch.WordTrace tailWord_2238756 prefixEnd_2238756 85152436750899858559567 := by
  unfold tailWord_2238756
  simp only [CollatzResearch.WordTrace]
  refine ⟨40827069738688417964772061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54436092984917890619696081 40827069738688417964772061)
  ·
    refine ⟨15310151152008156736789523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40827069738688417964772061 15310151152008156736789523)
    ·
      refine ⟨22965226728012235105184285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15310151152008156736789523 22965226728012235105184285)
      ·
        refine ⟨8611960023004588164444107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22965226728012235105184285 8611960023004588164444107)
        ·
          refine ⟨12917940034506882246666161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8611960023004588164444107 12917940034506882246666161)
          ·
            refine ⟨9688455025880161684999621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12917940034506882246666161 9688455025880161684999621)
            ·
              refine ⟨1816585317352530315937429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9688455025880161684999621 1816585317352530315937429)
              ·
                refine ⟨85152436750899858559567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1816585317352530315937429 85152436750899858559567)
                ·
                  rfl

theorem cell22_2238756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 6].length) (baseStart_2238756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238756 prefixEnd_2238756 := by exact prefixLift 2238756
  have htrace : WordTrace (prefixWord ++ tailWord_2238756) baseStart_2238756 baseEnd_2238756 := by
    simpa [prefixWord, tailWord_2238756, baseEnd_2238756] using wordTrace_append hprefix tailTrace_2238756
  have hstable : (prefixWord ++ tailWord_2238756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238756).length < 2 ^ (prefixWord ++ tailWord_2238756).sum := by decide
  have hdescent : baseEnd_2238756 < baseStart_2238756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238762 : List Nat := [3, 1, 4, 2, 3, 1, 1, 3, 4]
def baseStart_2238762 : Nat := 118140960795 + 2238762 * 2 ^ 59
def prefixEnd_2238762 : Nat := 4983230072969 + 3 ^ 40 * 2238762 * 2
def baseEnd_2238762 : Nat := 255457994893572237128695

theorem tailTrace_2238762 : CollatzResearch.WordTrace tailWord_2238762 prefixEnd_2238762 255457994893572237128695 := by
  unfold tailWord_2238762
  simp only [CollatzResearch.WordTrace]
  refine ⟨20413589578838774738565635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54436238876903399302841693 20413589578838774738565635)
  ·
    refine ⟨30620384368258162107848453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20413589578838774738565635 30620384368258162107848453)
    ·
      refine ⟨5741322069048405395221585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30620384368258162107848453 5741322069048405395221585)
      ·
        refine ⟨4305991551786304046416189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5741322069048405395221585 4305991551786304046416189)
        ·
          refine ⟨1614746831919864017406071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4305991551786304046416189 1614746831919864017406071)
          ·
            refine ⟨2422120247879796026109107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1614746831919864017406071 2422120247879796026109107)
            ·
              refine ⟨3633180371819694039163661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2422120247879796026109107 3633180371819694039163661)
              ·
                refine ⟨1362442639432385264686373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3633180371819694039163661 1362442639432385264686373)
                ·
                  refine ⟨255457994893572237128695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1362442639432385264686373 255457994893572237128695)
                  ·
                    rfl

theorem cell22_2238762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_2238762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238762 prefixEnd_2238762 := by exact prefixLift 2238762
  have htrace : WordTrace (prefixWord ++ tailWord_2238762) baseStart_2238762 baseEnd_2238762 := by
    simpa [prefixWord, tailWord_2238762, baseEnd_2238762] using wordTrace_append hprefix tailTrace_2238762
  have hstable : (prefixWord ++ tailWord_2238762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238762).length < 2 ^ (prefixWord ++ tailWord_2238762).sum := by decide
  have hdescent : baseEnd_2238762 < baseStart_2238762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238801 : List Nat := [1, 2, 2, 1, 4, 3, 1, 3, 5]
def baseStart_2238801 : Nat := 118140960795 + 2238801 * 2 ^ 59
def prefixEnd_2238801 : Nat := 4983230072969 + 3 ^ 40 * 2238801 * 2
def baseEnd_2238801 : Nat := 255462445059244536553655

theorem tailTrace_2238801 : CollatzResearch.WordTrace tailWord_2238801 prefixEnd_2238801 255462445059244536553655 := by
  unfold tailWord_2238801
  simp only [CollatzResearch.WordTrace]
  refine ⟨81655780762213808614932257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54437187174809205743288171 81655780762213808614932257)
  ·
    refine ⟨61241835571660356461199193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81655780762213808614932257 61241835571660356461199193)
    ·
      refine ⟨45931376678745267345899395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61241835571660356461199193 45931376678745267345899395)
      ·
        refine ⟨68897065018117901018849093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45931376678745267345899395 68897065018117901018849093)
        ·
          refine ⟨12918199690897106441034205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68897065018117901018849093 12918199690897106441034205)
          ·
            refine ⟨4844324884086414915387827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12918199690897106441034205 4844324884086414915387827)
            ·
              refine ⟨7266487326129622373081741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4844324884086414915387827 7266487326129622373081741)
              ·
                refine ⟨2724932747298608389905653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7266487326129622373081741 2724932747298608389905653)
                ·
                  refine ⟨255462445059244536553655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2724932747298608389905653 255462445059244536553655)
                  ·
                    rfl

theorem cell22_2238801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 5].length) (baseStart_2238801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238801 prefixEnd_2238801 := by exact prefixLift 2238801
  have htrace : WordTrace (prefixWord ++ tailWord_2238801) baseStart_2238801 baseEnd_2238801 := by
    simpa [prefixWord, tailWord_2238801, baseEnd_2238801] using wordTrace_append hprefix tailTrace_2238801
  have hstable : (prefixWord ++ tailWord_2238801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238801).length < 2 ^ (prefixWord ++ tailWord_2238801).sum := by decide
  have hdescent : baseEnd_2238801 < baseStart_2238801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238850 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_2238850 : Nat := 118140960795 + 2238850 * 2 ^ 59
def prefixEnd_2238850 : Nat := 4983230072969 + 3 ^ 40 * 2238850 * 2
def baseEnd_2238850 : Nat := 766404108879113815185815

theorem tailTrace_2238850 : CollatzResearch.WordTrace tailWord_2238850 prefixEnd_2238850 766404108879113815185815 := by
  unfold tailWord_2238850
  simp only [CollatzResearch.WordTrace]
  refine ⟨20414391984759072495866501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54438378626024193322310669 20414391984759072495866501)
  ·
    refine ⟨3827698497142326092974969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20414391984759072495866501 3827698497142326092974969)
    ·
      refine ⟨2870773872856744569731227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3827698497142326092974969 2870773872856744569731227)
      ·
        refine ⟨4306160809285116854596841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2870773872856744569731227 4306160809285116854596841)
        ·
          refine ⟨3229620606963837640947631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4306160809285116854596841 3229620606963837640947631)
          ·
            refine ⟨4844430910445756461421447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3229620606963837640947631 4844430910445756461421447)
            ·
              refine ⟨7266646365668634692132171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4844430910445756461421447 7266646365668634692132171)
              ·
                refine ⟨10899969548502952038198257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7266646365668634692132171 10899969548502952038198257)
                ·
                  refine ⟨8174977161377214028648693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10899969548502952038198257 8174977161377214028648693)
                  ·
                    refine ⟨766404108879113815185815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8174977161377214028648693 766404108879113815185815)
                    ·
                      rfl

theorem cell22_2238850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_2238850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238850 prefixEnd_2238850 := by exact prefixLift 2238850
  have htrace : WordTrace (prefixWord ++ tailWord_2238850) baseStart_2238850 baseEnd_2238850 := by
    simpa [prefixWord, tailWord_2238850, baseEnd_2238850] using wordTrace_append hprefix tailTrace_2238850
  have hstable : (prefixWord ++ tailWord_2238850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238850).length < 2 ^ (prefixWord ++ tailWord_2238850).sum := by decide
  have hdescent : baseEnd_2238850 < baseStart_2238850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238889 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 1, 9]
def baseStart_2238889 : Nat := 118140960795 + 2238889 * 2 ^ 59
def prefixEnd_2238889 : Nat := 4983230072969 + 3 ^ 40 * 2238889 * 2
def baseEnd_2238889 : Nat := 766417459376130713460695

theorem tailTrace_2238889 : CollatzResearch.WordTrace tailWord_2238889 prefixEnd_2238889 766417459376130713460695 := by
  unfold tailWord_2238889
  simp only [CollatzResearch.WordTrace]
  refine ⟨81658990385894999644135721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54439326923929999762757147 81658990385894999644135721)
  ·
    refine ⟨61244242789421249733101791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81658990385894999644135721 61244242789421249733101791)
    ·
      refine ⟨91866364184131874599652687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61244242789421249733101791 91866364184131874599652687)
      ·
        refine ⟨137799546276197811899479031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91866364184131874599652687 137799546276197811899479031)
        ·
          refine ⟨206699319414296717849218547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137799546276197811899479031 206699319414296717849218547)
          ·
            refine ⟨310048979121445076773827821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206699319414296717849218547 310048979121445076773827821)
            ·
              refine ⟨116268367170541903790185433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 310048979121445076773827821 116268367170541903790185433)
              ·
                refine ⟨87201275377906427842639075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116268367170541903790185433 87201275377906427842639075)
                ·
                  refine ⟨130801913066859641763958613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87201275377906427842639075 130801913066859641763958613)
                  ·
                    refine ⟨766417459376130713460695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 130801913066859641763958613 766417459376130713460695)
                    ·
                      rfl

theorem cell22_2238889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_2238889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238889 prefixEnd_2238889 := by exact prefixLift 2238889
  have htrace : WordTrace (prefixWord ++ tailWord_2238889) baseStart_2238889 baseEnd_2238889 := by
    simpa [prefixWord, tailWord_2238889, baseEnd_2238889] using wordTrace_append hprefix tailTrace_2238889
  have hstable : (prefixWord ++ tailWord_2238889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238889).length < 2 ^ (prefixWord ++ tailWord_2238889).sum := by decide
  have hdescent : baseEnd_2238889 < baseStart_2238889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238957 : List Nat := [1, 5, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_2238957 : Nat := 118140960795 + 2238957 * 2 ^ 59
def prefixEnd_2238957 : Nat := 4983230072969 + 3 ^ 40 * 2238957 * 2
def baseEnd_2238957 : Nat := 766440737165801202760487

theorem tailTrace_2238957 : CollatzResearch.WordTrace tailWord_2238957 prefixEnd_2238957 766440737165801202760487 := by
  unfold tailWord_2238957
  simp only [CollatzResearch.WordTrace]
  refine ⟨81661470549648647257611125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54440980366432431505074083 81661470549648647257611125)
  ·
    refine ⟨7655762864029560680401043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81661470549648647257611125 7655762864029560680401043)
    ·
      refine ⟨11483644296044341020601565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7655762864029560680401043 11483644296044341020601565)
      ·
        refine ⟨4306366611016627882725587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11483644296044341020601565 4306366611016627882725587)
        ·
          refine ⟨6459549916524941824088381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4306366611016627882725587 6459549916524941824088381)
          ·
            refine ⟨2422331218696853184033143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6459549916524941824088381 2422331218696853184033143)
            ·
              refine ⟨3633496828045279776049715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2422331218696853184033143 3633496828045279776049715)
              ·
                refine ⟨5450245242067919664074573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3633496828045279776049715 5450245242067919664074573)
                ·
                  refine ⟨2043841965775469874027965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5450245242067919664074573 2043841965775469874027965)
                  ·
                    refine ⟨766440737165801202760487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2043841965775469874027965 766440737165801202760487)
                    ·
                      rfl

theorem cell22_2238957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_2238957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238957 prefixEnd_2238957 := by exact prefixLift 2238957
  have htrace : WordTrace (prefixWord ++ tailWord_2238957) baseStart_2238957 baseEnd_2238957 := by
    simpa [prefixWord, tailWord_2238957, baseEnd_2238957] using wordTrace_append hprefix tailTrace_2238957
  have hstable : (prefixWord ++ tailWord_2238957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238957).length < 2 ^ (prefixWord ++ tailWord_2238957).sum := by decide
  have hdescent : baseEnd_2238957 < baseStart_2238957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2238981 : List Nat := [1, 3, 1, 1, 2, 2, 2, 4, 6]
def baseStart_2238981 : Nat := 118140960795 + 2238981 * 2 ^ 59
def prefixEnd_2238981 : Nat := 4983230072969 + 3 ^ 40 * 2238981 * 2
def baseEnd_2238981 : Nat := 255482984285424380053471

theorem tailTrace_2238981 : CollatzResearch.WordTrace tailWord_2238981 prefixEnd_2238981 255482984285424380053471 := by
  unfold tailWord_2238981
  simp only [CollatzResearch.WordTrace]
  refine ⟨81662345901561699356484797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54441563934374466237656531 81662345901561699356484797)
  ·
    refine ⟨30623379713085637258681799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81662345901561699356484797 30623379713085637258681799)
    ·
      refine ⟨45935069569628455888022699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30623379713085637258681799 45935069569628455888022699)
      ·
        refine ⟨68902604354442683832034049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45935069569628455888022699 68902604354442683832034049)
        ·
          refine ⟨51676953265832012874025537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68902604354442683832034049 51676953265832012874025537)
          ·
            refine ⟨38757714949374009655519153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51676953265832012874025537 38757714949374009655519153)
            ·
              refine ⟨29068286212030507241639365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38757714949374009655519153 29068286212030507241639365)
              ·
                refine ⟨5450303664755720107807381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29068286212030507241639365 5450303664755720107807381)
                ·
                  refine ⟨255482984285424380053471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5450303664755720107807381 255482984285424380053471)
                  ·
                    rfl

theorem cell22_2238981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_2238981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2238981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2238981 prefixEnd_2238981 := by exact prefixLift 2238981
  have htrace : WordTrace (prefixWord ++ tailWord_2238981) baseStart_2238981 baseEnd_2238981 := by
    simpa [prefixWord, tailWord_2238981, baseEnd_2238981] using wordTrace_append hprefix tailTrace_2238981
  have hstable : (prefixWord ++ tailWord_2238981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2238981).length < 2 ^ (prefixWord ++ tailWord_2238981).sum := by decide
  have hdescent : baseEnd_2238981 < baseStart_2238981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2238981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239013 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 4, 3]
def baseStart_2239013 : Nat := 118140960795 + 2239013 * 2 ^ 59
def prefixEnd_2239013 : Nat := 4983230072969 + 3 ^ 40 * 2239013 * 2
def baseEnd_2239013 : Nat := 766459907110235723360315

theorem tailTrace_2239013 : CollatzResearch.WordTrace tailWord_2239013 prefixEnd_2239013 766459907110235723360315 := by
  unfold tailWord_2239013
  simp only [CollatzResearch.WordTrace]
  refine ⟨81663513037445768821649693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54442342024963845881099795 81663513037445768821649693)
  ·
    refine ⟨30623817389042163308118635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81663513037445768821649693 30623817389042163308118635)
    ·
      refine ⟨45935726083563244962177953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30623817389042163308118635 45935726083563244962177953)
      ·
        refine ⟨34451794562672433721633465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45935726083563244962177953 34451794562672433721633465)
        ·
          refine ⟨25838845922004325291225099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34451794562672433721633465 25838845922004325291225099)
          ·
            refine ⟨38758268883006487936837649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25838845922004325291225099 38758268883006487936837649)
            ·
              refine ⟨29068701662254865952628237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38758268883006487936837649 29068701662254865952628237)
              ·
                refine ⟨10900763123345574732235589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29068701662254865952628237 10900763123345574732235589)
                ·
                  refine ⟨2043893085627295262294173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10900763123345574732235589 2043893085627295262294173)
                  ·
                    refine ⟨766459907110235723360315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2043893085627295262294173 766459907110235723360315)
                    ·
                      rfl

theorem cell22_2239013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_2239013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239013 prefixEnd_2239013 := by exact prefixLift 2239013
  have htrace : WordTrace (prefixWord ++ tailWord_2239013) baseStart_2239013 baseEnd_2239013 := by
    simpa [prefixWord, tailWord_2239013, baseEnd_2239013] using wordTrace_append hprefix tailTrace_2239013
  have hstable : (prefixWord ++ tailWord_2239013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239013).length < 2 ^ (prefixWord ++ tailWord_2239013).sum := by decide
  have hdescent : baseEnd_2239013 < baseStart_2239013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239030 : List Nat := [5, 1, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_2239030 : Nat := 118140960795 + 2239030 * 2 ^ 59
def prefixEnd_2239030 : Nat := 4983230072969 + 3 ^ 40 * 2239030 * 2
def baseEnd_2239030 : Nat := 766465726557653345685263

theorem tailTrace_2239030 : CollatzResearch.WordTrace tailWord_2239030 prefixEnd_2239030 766465726557653345685263 := by
  unfold tailWord_2239030
  simp only [CollatzResearch.WordTrace]
  refine ⟨5104008317399011295313659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54442755385589453816679029 5104008317399011295313659)
  ·
    refine ⟨7656012476098516942970489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5104008317399011295313659 7656012476098516942970489)
    ·
      refine ⟨5742009357073887707227867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7656012476098516942970489 5742009357073887707227867)
      ·
        refine ⟨8613014035610831560841801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5742009357073887707227867 8613014035610831560841801)
        ·
          refine ⟨6459760526708123670631351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8613014035610831560841801 6459760526708123670631351)
          ·
            refine ⟨9689640790062185505947027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6459760526708123670631351 9689640790062185505947027)
            ·
              refine ⟨14534461185093278258920541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9689640790062185505947027 14534461185093278258920541)
              ·
                refine ⟨5450422944409979347095203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14534461185093278258920541 5450422944409979347095203)
                ·
                  refine ⟨8175634416614969020642805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5450422944409979347095203 8175634416614969020642805)
                  ·
                    refine ⟨766465726557653345685263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8175634416614969020642805 766465726557653345685263)
                    ·
                      rfl

theorem cell22_2239030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_2239030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239030 prefixEnd_2239030 := by exact prefixLift 2239030
  have htrace : WordTrace (prefixWord ++ tailWord_2239030) baseStart_2239030 baseEnd_2239030 := by
    simpa [prefixWord, tailWord_2239030, baseEnd_2239030] using wordTrace_append hprefix tailTrace_2239030
  have hstable : (prefixWord ++ tailWord_2239030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239030).length < 2 ^ (prefixWord ++ tailWord_2239030).sum := by decide
  have hdescent : baseEnd_2239030 < baseStart_2239030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239045 : List Nat := [1, 3, 1, 1, 1, 7, 1, 1, 2, 4]
def baseStart_2239045 : Nat := 118140960795 + 2239045 * 2 ^ 59
def prefixEnd_2239045 : Nat := 4983230072969 + 3 ^ 40 * 2239045 * 2
def baseEnd_2239045 : Nat := 766470861364198306560217

theorem tailTrace_2239045 : CollatzResearch.WordTrace tailWord_2239045 prefixEnd_2239045 766470861364198306560217 := by
  unfold tailWord_2239045
  simp only [CollatzResearch.WordTrace]
  refine ⟨81664680173329838286814589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54443120115553225524543059 81664680173329838286814589)
  ·
    refine ⟨30624255064998689357555471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81664680173329838286814589 30624255064998689357555471)
    ·
      refine ⟨45936382597498034036333207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30624255064998689357555471 45936382597498034036333207)
      ·
        refine ⟨68904573896247051054499811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45936382597498034036333207 68904573896247051054499811)
        ·
          refine ⟨103356860844370576581749717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68904573896247051054499811 103356860844370576581749717)
          ·
            refine ⟨2422426426039935388634759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 103356860844370576581749717 2422426426039935388634759)
            ·
              refine ⟨3633639639059903082952139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2422426426039935388634759 3633639639059903082952139)
              ·
                refine ⟨5450459458589854624428209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3633639639059903082952139 5450459458589854624428209)
                ·
                  refine ⟨4087844593942390968321157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5450459458589854624428209 4087844593942390968321157)
                  ·
                    refine ⟨766470861364198306560217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4087844593942390968321157 766470861364198306560217)
                    ·
                      rfl

theorem cell22_2239045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_2239045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239045 prefixEnd_2239045 := by exact prefixLift 2239045
  have htrace : WordTrace (prefixWord ++ tailWord_2239045) baseStart_2239045 baseEnd_2239045 := by
    simpa [prefixWord, tailWord_2239045, baseEnd_2239045] using wordTrace_append hprefix tailTrace_2239045
  have hstable : (prefixWord ++ tailWord_2239045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239045).length < 2 ^ (prefixWord ++ tailWord_2239045).sum := by decide
  have hdescent : baseEnd_2239045 < baseStart_2239045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239056 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 1, 8]
def baseStart_2239056 : Nat := 118140960795 + 2239056 * 2 ^ 59
def prefixEnd_2239056 : Nat := 4983230072969 + 3 ^ 40 * 2239056 * 2
def baseEnd_2239056 : Nat := 766474626888997944535183

theorem tailTrace_2239056 : CollatzResearch.WordTrace tailWord_2239056 prefixEnd_2239056 766474626888997944535183 := by
  unfold tailWord_2239056
  simp only [CollatzResearch.WordTrace]
  refine ⟨40832540688144993582732511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54443387584193324776976681 40832540688144993582732511)
  ·
    refine ⟨61248811032217490374098767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40832540688144993582732511 61248811032217490374098767)
    ·
      refine ⟨91873216548326235561148151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61248811032217490374098767 91873216548326235561148151)
      ·
        refine ⟨137809824822489353341722227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91873216548326235561148151 137809824822489353341722227)
        ·
          refine ⟨206714737233734030012583341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137809824822489353341722227 206714737233734030012583341)
          ·
            refine ⟨77518026462650261254718753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206714737233734030012583341 77518026462650261254718753)
            ·
              refine ⟨58138519846987695941039065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77518026462650261254718753 58138519846987695941039065)
              ·
                refine ⟨43603889885240771955779299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58138519846987695941039065 43603889885240771955779299)
                ·
                  refine ⟨65405834827861157933668949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43603889885240771955779299 65405834827861157933668949)
                  ·
                    refine ⟨766474626888997944535183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65405834827861157933668949 766474626888997944535183)
                    ·
                      rfl

theorem cell22_2239056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_2239056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239056 prefixEnd_2239056 := by exact prefixLift 2239056
  have htrace : WordTrace (prefixWord ++ tailWord_2239056) baseStart_2239056 baseEnd_2239056 := by
    simpa [prefixWord, tailWord_2239056, baseEnd_2239056] using wordTrace_append hprefix tailTrace_2239056
  have hstable : (prefixWord ++ tailWord_2239056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239056).length < 2 ^ (prefixWord ++ tailWord_2239056).sum := by decide
  have hdescent : baseEnd_2239056 < baseStart_2239056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239075 : List Nat := [1, 1, 1, 5, 1, 2, 4, 1, 3, 3]
def baseStart_2239075 : Nat := 118140960795 + 2239075 * 2 ^ 59
def prefixEnd_2239075 : Nat := 4983230072969 + 3 ^ 40 * 2239075 * 2
def baseEnd_2239075 : Nat := 766481130977288228310125

theorem tailTrace_2239075 : CollatzResearch.WordTrace tailWord_2239075 prefixEnd_2239075 766481130977288228310125 := by
  unfold tailWord_2239075
  simp only [CollatzResearch.WordTrace]
  refine ⟨81665774363221153410406679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54443849575480768940271119 81665774363221153410406679)
  ·
    refine ⟨122498661544831730115610019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81665774363221153410406679 122498661544831730115610019)
    ·
      refine ⟨183747992317247595173415029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122498661544831730115610019 183747992317247595173415029)
      ·
        refine ⟨17226374279741962047507659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 183747992317247595173415029 17226374279741962047507659)
        ·
          refine ⟨25839561419612943071261489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17226374279741962047507659 25839561419612943071261489)
          ·
            refine ⟨19379671064709707303446117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25839561419612943071261489 19379671064709707303446117)
            ·
              refine ⟨3633688324633070119396147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19379671064709707303446117 3633688324633070119396147)
              ·
                refine ⟨5450532486949605179094221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3633688324633070119396147 5450532486949605179094221)
                ·
                  refine ⟨2043949682606101942160333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5450532486949605179094221 2043949682606101942160333)
                  ·
                    refine ⟨766481130977288228310125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2043949682606101942160333 766481130977288228310125)
                    ·
                      rfl

theorem cell22_2239075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 3].length) (baseStart_2239075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239075 prefixEnd_2239075 := by exact prefixLift 2239075
  have htrace : WordTrace (prefixWord ++ tailWord_2239075) baseStart_2239075 baseEnd_2239075 := by
    simpa [prefixWord, tailWord_2239075, baseEnd_2239075] using wordTrace_append hprefix tailTrace_2239075
  have hstable : (prefixWord ++ tailWord_2239075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239075).length < 2 ^ (prefixWord ++ tailWord_2239075).sum := by decide
  have hdescent : baseEnd_2239075 < baseStart_2239075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239094 : List Nat := [5, 1, 1, 2, 4, 1, 2, 6]
def baseStart_2239094 : Nat := 118140960795 + 2239094 * 2 ^ 59
def prefixEnd_2239094 : Nat := 4983230072969 + 3 ^ 40 * 2239094 * 2
def baseEnd_2239094 : Nat := 85165292785064279120563

theorem tailTrace_2239094 : CollatzResearch.WordTrace tailWord_2239094 prefixEnd_2239094 85165292785064279120563 := by
  unfold tailWord_2239094
  simp only [CollatzResearch.WordTrace]
  refine ⟨5104154209384519978459271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54444311566768213103565557 5104154209384519978459271)
  ·
    refine ⟨7656231314076779967688907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5104154209384519978459271 7656231314076779967688907)
    ·
      refine ⟨11484346971115169951533361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7656231314076779967688907 11484346971115169951533361)
      ·
        refine ⟨8613260228336377463650021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11484346971115169951533361 8613260228336377463650021)
        ·
          refine ⟨1614986292813070774434379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8613260228336377463650021 1614986292813070774434379)
          ·
            refine ⟨2422479439219606161651569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1614986292813070774434379 2422479439219606161651569)
            ·
              refine ⟨1816859579414704621238677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2422479439219606161651569 1816859579414704621238677)
              ·
                refine ⟨85165292785064279120563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1816859579414704621238677 85165292785064279120563)
                ·
                  rfl

theorem cell22_2239094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_2239094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239094 prefixEnd_2239094 := by exact prefixLift 2239094
  have htrace : WordTrace (prefixWord ++ tailWord_2239094) baseStart_2239094 baseEnd_2239094 := by
    simpa [prefixWord, tailWord_2239094, baseEnd_2239094] using wordTrace_append hprefix tailTrace_2239094
  have hstable : (prefixWord ++ tailWord_2239094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239094).length < 2 ^ (prefixWord ++ tailWord_2239094).sum := by decide
  have hdescent : baseEnd_2239094 < baseStart_2239094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239109 : List Nat := [1, 3, 1, 1, 4, 4, 1, 3, 1, 3]
def baseStart_2239109 : Nat := 118140960795 + 2239109 * 2 ^ 59
def prefixEnd_2239109 : Nat := 4983230072969 + 3 ^ 40 * 2239109 * 2
def baseEnd_2239109 : Nat := 766492769872123472960021

theorem tailTrace_2239109 : CollatzResearch.WordTrace tailWord_2239109 prefixEnd_2239109 766492769872123472960021 := by
  unfold tailWord_2239109
  simp only [CollatzResearch.WordTrace]
  refine ⟨81667014445097977217144381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54444676296731984811429587 81667014445097977217144381)
  ·
    refine ⟨30625130416911741456429143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81667014445097977217144381 30625130416911741456429143)
    ·
      refine ⟨45937695625367612184643715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30625130416911741456429143 45937695625367612184643715)
      ·
        refine ⟨68906543438051418276965573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45937695625367612184643715 68906543438051418276965573)
        ·
          refine ⟨12919976894634640926931045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68906543438051418276965573 12919976894634640926931045)
          ·
            refine ⟨2422495667743995173799571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12919976894634640926931045 2422495667743995173799571)
            ·
              refine ⟨3633743501615992760699357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2422495667743995173799571 3633743501615992760699357)
              ·
                refine ⟨1362653813105997285262259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3633743501615992760699357 1362653813105997285262259)
                ·
                  refine ⟨2043980719658995927893389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1362653813105997285262259 2043980719658995927893389)
                  ·
                    refine ⟨766492769872123472960021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2043980719658995927893389 766492769872123472960021)
                    ·
                      rfl

theorem cell22_2239109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 1, 3].length) (baseStart_2239109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239109 prefixEnd_2239109 := by exact prefixLift 2239109
  have htrace : WordTrace (prefixWord ++ tailWord_2239109) baseStart_2239109 baseEnd_2239109 := by
    simpa [prefixWord, tailWord_2239109, baseEnd_2239109] using wordTrace_append hprefix tailTrace_2239109
  have hstable : (prefixWord ++ tailWord_2239109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239109).length < 2 ^ (prefixWord ++ tailWord_2239109).sum := by decide
  have hdescent : baseEnd_2239109 < baseStart_2239109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239165 : List Nat := [1, 4, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_2239165 : Nat := 118140960795 + 2239165 * 2 ^ 59
def prefixEnd_2239165 : Nat := 4983230072969 + 3 ^ 40 * 2239165 * 2
def baseEnd_2239165 : Nat := 766511939816557993559849

theorem tailTrace_2239165 : CollatzResearch.WordTrace tailWord_2239165 prefixEnd_2239165 766511939816557993559849 := by
  unfold tailWord_2239165
  simp only [CollatzResearch.WordTrace]
  refine ⟨81669056932895098781182949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54446037955263399187455299 81669056932895098781182949)
  ·
    refine ⟨15312948174917831021471803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81669056932895098781182949 15312948174917831021471803)
    ·
      refine ⟨22969422262376746532207705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15312948174917831021471803 22969422262376746532207705)
      ·
        refine ⟨17227066696782559899155779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22969422262376746532207705 17227066696782559899155779)
        ·
          refine ⟨25840600045173839848733669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17227066696782559899155779 25840600045173839848733669)
          ·
            refine ⟨4845112508470094971637563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25840600045173839848733669 4845112508470094971637563)
            ·
              refine ⟨7267668762705142457456345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4845112508470094971637563 7267668762705142457456345)
              ·
                refine ⟨5450751572028856843092259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7267668762705142457456345 5450751572028856843092259)
                ·
                  refine ⟨8176127358043285264638389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5450751572028856843092259 8176127358043285264638389)
                  ·
                    refine ⟨766511939816557993559849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8176127358043285264638389 766511939816557993559849)
                    ·
                      rfl

theorem cell22_2239165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_2239165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239165 prefixEnd_2239165 := by exact prefixLift 2239165
  have htrace : WordTrace (prefixWord ++ tailWord_2239165) baseStart_2239165 baseEnd_2239165 := by
    simpa [prefixWord, tailWord_2239165, baseEnd_2239165] using wordTrace_append hprefix tailTrace_2239165
  have hstable : (prefixWord ++ tailWord_2239165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239165).length < 2 ^ (prefixWord ++ tailWord_2239165).sum := by decide
  have hdescent : baseEnd_2239165 < baseStart_2239165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239178 : List Nat := [3, 1, 2, 1, 4, 11]
def baseStart_2239178 : Nat := 118140960795 + 2239178 * 2 ^ 59
def prefixEnd_2239178 : Nat := 4983230072969 + 3 ^ 40 * 2239178 * 2
def baseEnd_2239178 : Nat := 9463165308422596209689

theorem tailTrace_2239178 : CollatzResearch.WordTrace tailWord_2239178 prefixEnd_2239178 9463165308422596209689 := by
  unfold tailWord_2239178
  simp only [CollatzResearch.WordTrace]
  refine ⟨20417382770462000500351547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54446354054565334667604125 20417382770462000500351547)
  ·
    refine ⟨30626074155693000750527321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20417382770462000500351547 30626074155693000750527321)
    ·
      refine ⟨22969555616769750562895491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30626074155693000750527321 22969555616769750562895491)
      ·
        refine ⟨34454333425154625844343237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22969555616769750562895491 34454333425154625844343237)
        ·
          refine ⟨6460187517216492345814357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34454333425154625844343237 6460187517216492345814357)
          ·
            refine ⟨9463165308422596209689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6460187517216492345814357 9463165308422596209689)
            ·
              rfl

theorem cell22_2239178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 11].length) (baseStart_2239178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239178 prefixEnd_2239178 := by exact prefixLift 2239178
  have htrace : WordTrace (prefixWord ++ tailWord_2239178) baseStart_2239178 baseEnd_2239178 := by
    simpa [prefixWord, tailWord_2239178, baseEnd_2239178] using wordTrace_append hprefix tailTrace_2239178
  have hstable : (prefixWord ++ tailWord_2239178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239178).length < 2 ^ (prefixWord ++ tailWord_2239178).sum := by decide
  have hdescent : baseEnd_2239178 < baseStart_2239178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2239182 : List Nat := [4, 1, 1, 1, 3, 2, 1, 4, 2, 3]
def baseStart_2239182 : Nat := 118140960795 + 2239182 * 2 ^ 59
def prefixEnd_2239182 : Nat := 4983230072969 + 3 ^ 40 * 2239182 * 2
def baseEnd_2239182 : Nat := 766517759263975615884797

theorem tailTrace_2239182 : CollatzResearch.WordTrace tailWord_2239182 prefixEnd_2239182 766517759263975615884797 := by
  unfold tailWord_2239182
  simp only [CollatzResearch.WordTrace]
  refine ⟨10208709621729188835568975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54446451315889007123034533 10208709621729188835568975)
  ·
    refine ⟨15313064432593783253353463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10208709621729188835568975 15313064432593783253353463)
    ·
      refine ⟨22969596648890674880030195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15313064432593783253353463 22969596648890674880030195)
      ·
        refine ⟨34454394973336012320045293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22969596648890674880030195 34454394973336012320045293)
        ·
          refine ⟨12920398115001004620016985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34454394973336012320045293 12920398115001004620016985)
          ·
            refine ⟨9690298586250753465012739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12920398115001004620016985 9690298586250753465012739)
            ·
              refine ⟨14535447879376130197519109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9690298586250753465012739 14535447879376130197519109)
              ·
                refine ⟨2725396477383024412034833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14535447879376130197519109 2725396477383024412034833)
                ·
                  refine ⟨2044047358037268309026125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2725396477383024412034833 2044047358037268309026125)
                  ·
                    refine ⟨766517759263975615884797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2044047358037268309026125 766517759263975615884797)
                    ·
                      rfl

theorem cell22_2239182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_2239182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2239182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2239182 prefixEnd_2239182 := by exact prefixLift 2239182
  have htrace : WordTrace (prefixWord ++ tailWord_2239182) baseStart_2239182 baseEnd_2239182 := by
    simpa [prefixWord, tailWord_2239182, baseEnd_2239182] using wordTrace_append hprefix tailTrace_2239182
  have hstable : (prefixWord ++ tailWord_2239182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2239182).length < 2 ^ (prefixWord ++ tailWord_2239182).sum := by decide
  have hdescent : baseEnd_2239182 < baseStart_2239182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2239182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
