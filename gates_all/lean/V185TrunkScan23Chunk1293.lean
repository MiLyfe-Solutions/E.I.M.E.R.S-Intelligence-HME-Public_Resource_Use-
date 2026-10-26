import V185TrunkScan23Chunk1292

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7658284 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 3, 3, 2]
def baseStart_7658284 : Nat := 118140960795 + 7658284 * 2 ^ 59
def prefixEnd_7658284 : Nat := 4983230072969 + 3 ^ 40 * 7658284 * 2
def baseEnd_7658284 : Nat := 3932380680637020162330199

theorem tailTrace_7658284 : CollatzResearch.WordTrace tailWord_7658284 prefixEnd_7658284 3932380680637020162330199 := by
  unfold tailWord_7658284
  simp only [CollatzResearch.WordTrace]
  refine ⟨139660282293676236811310953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186213709724901649081747937 139660282293676236811310953)
  ·
    refine ⟨104745211720257177608483215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139660282293676236811310953 104745211720257177608483215)
    ·
      refine ⟨157117817580385766412724823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104745211720257177608483215 157117817580385766412724823)
      ·
        refine ⟨235676726370578649619087235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157117817580385766412724823 235676726370578649619087235)
        ·
          refine ⟨353515089555867974428630853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235676726370578649619087235 353515089555867974428630853)
          ·
            refine ⟨66284079291725245205368285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 353515089555867974428630853 66284079291725245205368285)
            ·
              refine ⟨24856529734396966952013107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66284079291725245205368285 24856529734396966952013107)
              ·
                refine ⟨37284794601595450428019661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24856529734396966952013107 37284794601595450428019661)
                ·
                  refine ⟨13981797975598293910507373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37284794601595450428019661 13981797975598293910507373)
                  ·
                    refine ⟨5243174240849360216440265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13981797975598293910507373 5243174240849360216440265)
                    ·
                      refine ⟨3932380680637020162330199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5243174240849360216440265 3932380680637020162330199)
                      ·
                        rfl

theorem cell23_7658284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 3, 2].length) (baseStart_7658284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658284 prefixEnd_7658284 := by exact prefixLift 7658284
  have htrace : WordTrace (prefixWord ++ tailWord_7658284) baseStart_7658284 baseEnd_7658284 := by
    simpa [prefixWord, tailWord_7658284, baseEnd_7658284] using wordTrace_append hprefix tailTrace_7658284
  have hstable : (prefixWord ++ tailWord_7658284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658284).length < 2 ^ (prefixWord ++ tailWord_7658284).sum := by decide
  have hdescent : baseEnd_7658284 < baseStart_7658284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658324 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_7658324 : Nat := 118140960795 + 7658324 * 2 ^ 59
def prefixEnd_7658324 : Nat := 4983230072969 + 3 ^ 40 * 7658324 * 2
def baseEnd_7658324 : Nat := 1310800406621066668610005

theorem tailTrace_7658324 : CollatzResearch.WordTrace tailWord_7658324 prefixEnd_7658324 1310800406621066668610005 := by
  unfold tailWord_7658324
  simp only [CollatzResearch.WordTrace]
  refine ⟨139661011753603780227039013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186214682338138373636052017 139661011753603780227039013)
  ·
    refine ⟨26186439703800708792569815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139661011753603780227039013 26186439703800708792569815)
    ·
      refine ⟨39279659555701063188854723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26186439703800708792569815 39279659555701063188854723)
      ·
        refine ⟨58919489333551594783282085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39279659555701063188854723 58919489333551594783282085)
        ·
          refine ⟨11047404250040924021865391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58919489333551594783282085 11047404250040924021865391)
          ·
            refine ⟨16571106375061386032798087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11047404250040924021865391 16571106375061386032798087)
            ·
              refine ⟨24856659562592079049197131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16571106375061386032798087 24856659562592079049197131)
              ·
                refine ⟨37284989343888118573795697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24856659562592079049197131 37284989343888118573795697)
                ·
                  refine ⟨27963742007916088930346773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37284989343888118573795697 27963742007916088930346773)
                  ·
                    refine ⟨1310800406621066668610005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27963742007916088930346773 1310800406621066668610005)
                    ·
                      rfl

theorem cell23_7658324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_7658324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658324 prefixEnd_7658324 := by exact prefixLift 7658324
  have htrace : WordTrace (prefixWord ++ tailWord_7658324) baseStart_7658324 baseEnd_7658324 := by
    simpa [prefixWord, tailWord_7658324, baseEnd_7658324] using wordTrace_append hprefix tailTrace_7658324
  have hstable : (prefixWord ++ tailWord_7658324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658324).length < 2 ^ (prefixWord ++ tailWord_7658324).sum := by decide
  have hdescent : baseEnd_7658324 < baseStart_7658324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658327 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 4]
def baseStart_7658327 : Nat := 118140960795 + 7658327 * 2 ^ 59
def prefixEnd_7658327 : Nat := 4983230072969 + 3 ^ 40 * 7658327 * 2
def baseEnd_7658327 : Nat := 3932402760305163494092501

theorem tailTrace_7658327 : CollatzResearch.WordTrace tailWord_7658327 prefixEnd_7658327 3932402760305163494092501 := by
  unfold tailWord_7658327
  simp only [CollatzResearch.WordTrace]
  refine ⟨279322132926196691966437235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186214755284131127977624823 279322132926196691966437235)
  ·
    refine ⟨418983199389295037949655853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279322132926196691966437235 418983199389295037949655853)
    ·
      refine ⟨157118699770985639231120945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418983199389295037949655853 157118699770985639231120945)
      ·
        refine ⟨117839024828239229423340709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157118699770985639231120945 117839024828239229423340709)
        ·
          refine ⟨22094817155294855516876383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117839024828239229423340709 22094817155294855516876383)
          ·
            refine ⟨33142225732942283275314575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22094817155294855516876383 33142225732942283275314575)
            ·
              refine ⟨49713338599413424912971863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33142225732942283275314575 49713338599413424912971863)
              ·
                refine ⟨74570007899120137369457795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49713338599413424912971863 74570007899120137369457795)
                ·
                  refine ⟨111855011848680206054186693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74570007899120137369457795 111855011848680206054186693)
                  ·
                    refine ⟨20972814721627538635160005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111855011848680206054186693 20972814721627538635160005)
                    ·
                      refine ⟨3932402760305163494092501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20972814721627538635160005 3932402760305163494092501)
                      ·
                        rfl

theorem cell23_7658327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_7658327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658327 prefixEnd_7658327 := by exact prefixLift 7658327
  have htrace : WordTrace (prefixWord ++ tailWord_7658327) baseStart_7658327 baseEnd_7658327 := by
    simpa [prefixWord, tailWord_7658327, baseEnd_7658327] using wordTrace_append hprefix tailTrace_7658327
  have hstable : (prefixWord ++ tailWord_7658327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658327).length < 2 ^ (prefixWord ++ tailWord_7658327).sum := by decide
  have hdescent : baseEnd_7658327 < baseStart_7658327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658354 : List Nat := [3, 2, 1, 2, 1, 1, 3, 5, 5]
def baseStart_7658354 : Nat := 118140960795 + 7658354 * 2 ^ 59
def prefixEnd_7658354 : Nat := 4983230072969 + 3 ^ 40 * 7658354 * 2
def baseEnd_7658354 : Nat := 436935180475870543161653

theorem tailTrace_7658354 : CollatzResearch.WordTrace tailWord_7658354 prefixEnd_7658354 436935180475870543161653 := by
  unfold tailWord_7658354
  simp only [CollatzResearch.WordTrace]
  refine ⟨69830779424274718894417529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186215411798065917051780077 69830779424274718894417529)
  ·
    refine ⟨52373084568206039170813147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69830779424274718894417529 52373084568206039170813147)
    ·
      refine ⟨78559626852309058756219721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52373084568206039170813147 78559626852309058756219721)
      ·
        refine ⟨58919720139231794067164791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78559626852309058756219721 58919720139231794067164791)
        ·
          refine ⟨88379580208847691100747187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58919720139231794067164791 88379580208847691100747187)
          ·
            refine ⟨132569370313271536651120781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88379580208847691100747187 132569370313271536651120781)
            ·
              refine ⟨49713513867476826244170293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132569370313271536651120781 49713513867476826244170293)
              ·
                refine ⟨4660641925075952460390965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49713513867476826244170293 4660641925075952460390965)
                ·
                  refine ⟨436935180475870543161653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4660641925075952460390965 436935180475870543161653)
                  ·
                    rfl

theorem cell23_7658354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_7658354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658354 prefixEnd_7658354 := by exact prefixLift 7658354
  have htrace : WordTrace (prefixWord ++ tailWord_7658354) baseStart_7658354 baseEnd_7658354 := by
    simpa [prefixWord, tailWord_7658354, baseEnd_7658354] using wordTrace_append hprefix tailTrace_7658354
  have hstable : (prefixWord ++ tailWord_7658354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658354).length < 2 ^ (prefixWord ++ tailWord_7658354).sum := by decide
  have hdescent : baseEnd_7658354 < baseStart_7658354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658367 : List Nat := [1, 1, 2, 2, 1, 1, 4, 4, 2, 5]
def baseStart_7658367 : Nat := 118140960795 + 7658367 * 2 ^ 59
def prefixEnd_7658367 : Nat := 4983230072969 + 3 ^ 40 * 7658367 * 2
def baseEnd_7658367 : Nat := 1310807766510447779197439

theorem tailTrace_7658367 : CollatzResearch.WordTrace tailWord_7658367 prefixEnd_7658367 1310807766510447779197439 := by
  unfold tailWord_7658367
  simp only [CollatzResearch.WordTrace]
  refine ⟨279323591846051778797893355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186215727897367852531928903 279323591846051778797893355)
  ·
    refine ⟨418985387769077668196840033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279323591846051778797893355 418985387769077668196840033)
    ·
      refine ⟨314239040826808251147630025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418985387769077668196840033 314239040826808251147630025)
      ·
        refine ⟨235679280620106188360722519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314239040826808251147630025 235679280620106188360722519)
        ·
          refine ⟨353518920930159282541083779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235679280620106188360722519 353518920930159282541083779)
          ·
            refine ⟨530278381395238923811625669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353518920930159282541083779 530278381395238923811625669)
            ·
              refine ⟨99427196511607298214679813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 530278381395238923811625669 99427196511607298214679813)
              ·
                refine ⟨18642599345926368415252465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99427196511607298214679813 18642599345926368415252465)
                ·
                  refine ⟨13981949509444776311439349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18642599345926368415252465 13981949509444776311439349)
                  ·
                    refine ⟨1310807766510447779197439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13981949509444776311439349 1310807766510447779197439)
                    ·
                      rfl

theorem cell23_7658367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 5].length) (baseStart_7658367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658367 prefixEnd_7658367 := by exact prefixLift 7658367
  have htrace : WordTrace (prefixWord ++ tailWord_7658367) baseStart_7658367 baseEnd_7658367 := by
    simpa [prefixWord, tailWord_7658367, baseEnd_7658367] using wordTrace_append hprefix tailTrace_7658367
  have hstable : (prefixWord ++ tailWord_7658367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658367).length < 2 ^ (prefixWord ++ tailWord_7658367).sum := by decide
  have hdescent : baseEnd_7658367 < baseStart_7658367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658387 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 4]
def baseStart_7658387 : Nat := 118140960795 + 7658387 * 2 ^ 59
def prefixEnd_7658387 : Nat := 4983230072969 + 3 ^ 40 * 7658387 * 2
def baseEnd_7658387 : Nat := 3932433569144433259342225

theorem tailTrace_7658387 : CollatzResearch.WordTrace tailWord_7658387 prefixEnd_7658387 3932433569144433259342225 := by
  unfold tailWord_7658387
  simp only [CollatzResearch.WordTrace]
  refine ⟨279324321305979322213621415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186216214203986214809080943 279324321305979322213621415)
  ·
    refine ⟨418986481958968983320432123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279324321305979322213621415 418986481958968983320432123)
    ·
      refine ⟨628479722938453474980648185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418986481958968983320432123 628479722938453474980648185)
      ·
        refine ⟨471359792203840106235486139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628479722938453474980648185 471359792203840106235486139)
        ·
          refine ⟨707039688305760159353229209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471359792203840106235486139 707039688305760159353229209)
          ·
            refine ⟨530279766229320119514921907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707039688305760159353229209 530279766229320119514921907)
            ·
              refine ⟨795419649343980179272382861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530279766229320119514921907 795419649343980179272382861)
              ·
                refine ⟨298282368503992567227143573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 795419649343980179272382861 298282368503992567227143573)
                ·
                  refine ⟨13981986023624651588772355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 298282368503992567227143573 13981986023624651588772355)
                  ·
                    refine ⟨20972979035436977383158533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13981986023624651588772355 20972979035436977383158533)
                    ·
                      refine ⟨3932433569144433259342225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20972979035436977383158533 3932433569144433259342225)
                      ·
                        rfl

theorem cell23_7658387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 4].length) (baseStart_7658387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658387 prefixEnd_7658387 := by exact prefixLift 7658387
  have htrace : WordTrace (prefixWord ++ tailWord_7658387) baseStart_7658387 baseEnd_7658387 := by
    simpa [prefixWord, tailWord_7658387, baseEnd_7658387] using wordTrace_append hprefix tailTrace_7658387
  have hstable : (prefixWord ++ tailWord_7658387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658387).length < 2 ^ (prefixWord ++ tailWord_7658387).sum := by decide
  have hdescent : baseEnd_7658387 < baseStart_7658387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658397 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 2, 8]
def baseStart_7658397 : Nat := 118140960795 + 7658397 * 2 ^ 59
def prefixEnd_7658397 : Nat := 4983230072969 + 3 ^ 40 * 7658397 * 2
def baseEnd_7658397 : Nat := 1310812901316992740072393

theorem tailTrace_7658397 : CollatzResearch.WordTrace tailWord_7658397 prefixEnd_7658397 1310812901316992740072393 := by
  unfold tailWord_7658397
  simp only [CollatzResearch.WordTrace]
  refine ⟨279324686035943093921485445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186216457357295395947656963 279324686035943093921485445)
  ·
    refine ⟨52373378631739330110278521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279324686035943093921485445 52373378631739330110278521)
    ·
      refine ⟨39280033973804497582708891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52373378631739330110278521 39280033973804497582708891)
      ·
        refine ⟨58920050960706746374063337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39280033973804497582708891 58920050960706746374063337)
        ·
          refine ⟨44190038220530059780547503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58920050960706746374063337 44190038220530059780547503)
          ·
            refine ⟨66285057330795089670821255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44190038220530059780547503 66285057330795089670821255)
            ·
              refine ⟨99427585996192634506231883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66285057330795089670821255 99427585996192634506231883)
              ·
                refine ⟨149141378994288951759347825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99427585996192634506231883 149141378994288951759347825)
                ·
                  refine ⟨111856034245716713819510869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149141378994288951759347825 111856034245716713819510869)
                  ·
                    refine ⟨1310812901316992740072393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111856034245716713819510869 1310812901316992740072393)
                    ·
                      rfl

theorem cell23_7658397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_7658397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658397 prefixEnd_7658397 := by exact prefixLift 7658397
  have htrace : WordTrace (prefixWord ++ tailWord_7658397) baseStart_7658397 baseEnd_7658397 := by
    simpa [prefixWord, tailWord_7658397, baseEnd_7658397] using wordTrace_append hprefix tailTrace_7658397
  have hstable : (prefixWord ++ tailWord_7658397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658397).length < 2 ^ (prefixWord ++ tailWord_7658397).sum := by decide
  have hdescent : baseEnd_7658397 < baseStart_7658397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658404 : List Nat := [2, 3, 1, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_7658404 : Nat := 118140960795 + 7658404 * 2 ^ 59
def prefixEnd_7658404 : Nat := 4983230072969 + 3 ^ 40 * 7658404 * 2
def baseEnd_7658404 : Nat := 3932442298315559692829647

theorem tailTrace_7658404 : CollatzResearch.WordTrace tailWord_7658404 prefixEnd_7658404 3932442298315559692829647 := by
  unfold tailWord_7658404
  simp only [CollatzResearch.WordTrace]
  refine ⟨139662470673458867058495133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186216627564611822744660177 139662470673458867058495133)
  ·
    refine ⟨52373426502547075146935675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139662470673458867058495133 52373426502547075146935675)
    ·
      refine ⟨78560139753820612720403513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52373426502547075146935675 78560139753820612720403513)
      ·
        refine ⟨58920104815365459540302635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78560139753820612720403513 58920104815365459540302635)
        ·
          refine ⟨88380157223048189310453953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58920104815365459540302635 88380157223048189310453953)
          ·
            refine ⟨66285117917286141982840465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88380157223048189310453953 66285117917286141982840465)
            ·
              refine ⟨49713838437964606487130349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66285117917286141982840465 49713838437964606487130349)
              ·
                refine ⟨18642689414236727432673881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49713838437964606487130349 18642689414236727432673881)
                ·
                  refine ⟨13982017060677545574505411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18642689414236727432673881 13982017060677545574505411)
                  ·
                    refine ⟨20973025591016318361758117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13982017060677545574505411 20973025591016318361758117)
                    ·
                      refine ⟨3932442298315559692829647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20973025591016318361758117 3932442298315559692829647)
                      ·
                        rfl

theorem cell23_7658404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_7658404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658404 prefixEnd_7658404 := by exact prefixLift 7658404
  have htrace : WordTrace (prefixWord ++ tailWord_7658404) baseStart_7658404 baseEnd_7658404 := by
    simpa [prefixWord, tailWord_7658404, baseEnd_7658404] using wordTrace_append hprefix tailTrace_7658404
  have hstable : (prefixWord ++ tailWord_7658404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658404).length < 2 ^ (prefixWord ++ tailWord_7658404).sum := by decide
  have hdescent : baseEnd_7658404 < baseStart_7658404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658422 : List Nat := [5, 1, 4, 1, 2, 1, 1, 1, 7]
def baseStart_7658422 : Nat := 118140960795 + 7658422 * 2 ^ 59
def prefixEnd_7658422 : Nat := 4983230072969 + 3 ^ 40 * 7658422 * 2
def baseEnd_7658422 : Nat := 436939060107482291378285

theorem tailTrace_7658422 : CollatzResearch.WordTrace tailWord_7658422 prefixEnd_7658422 436939060107482291378285 := by
  unfold tailWord_7658422
  simp only [CollatzResearch.WordTrace]
  refine ⟨17457849866303282699446595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186217065240568348794097013 17457849866303282699446595)
  ·
    refine ⟨26186774799454924049169893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17457849866303282699446595 26186774799454924049169893)
    ·
      refine ⟨4910020274897798259219355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26186774799454924049169893 4910020274897798259219355)
      ·
        refine ⟨7365030412346697388829033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4910020274897798259219355 7365030412346697388829033)
        ·
          refine ⟨5523772809260023041621775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7365030412346697388829033 5523772809260023041621775)
          ·
            refine ⟨8285659213890034562432663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5523772809260023041621775 8285659213890034562432663)
            ·
              refine ⟨12428488820835051843648995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8285659213890034562432663 12428488820835051843648995)
              ·
                refine ⟨18642733231252577765473493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12428488820835051843648995 18642733231252577765473493)
                ·
                  refine ⟨436939060107482291378285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18642733231252577765473493 436939060107482291378285)
                  ·
                    rfl

theorem cell23_7658422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_7658422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658422 prefixEnd_7658422 := by exact prefixLift 7658422
  have htrace : WordTrace (prefixWord ++ tailWord_7658422) baseStart_7658422 baseEnd_7658422 := by
    simpa [prefixWord, tailWord_7658422, baseEnd_7658422] using wordTrace_append hprefix tailTrace_7658422
  have hstable : (prefixWord ++ tailWord_7658422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658422).length < 2 ^ (prefixWord ++ tailWord_7658422).sum := by decide
  have hdescent : baseEnd_7658422 < baseStart_7658422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658424 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 4, 2, 3]
def baseStart_7658424 : Nat := 118140960795 + 7658424 * 2 ^ 59
def prefixEnd_7658424 : Nat := 4983230072969 + 3 ^ 40 * 7658424 * 2
def baseEnd_7658424 : Nat := 3932452567928649614579555

theorem tailTrace_7658424 : CollatzResearch.WordTrace tailWord_7658424 prefixEnd_7658424 3932452567928649614579555 := by
  unfold tailWord_7658424
  simp only [CollatzResearch.WordTrace]
  refine ⟨139662835403422638766359163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186217113871230185021812217 139662835403422638766359163)
  ·
    refine ⟨209494253105133958149538745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139662835403422638766359163 209494253105133958149538745)
    ·
      refine ⟨157120689828850468612154059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209494253105133958149538745 157120689828850468612154059)
      ·
        refine ⟨235681034743275702918231089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157120689828850468612154059 235681034743275702918231089)
        ·
          refine ⟨176760776057456777188673317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235681034743275702918231089 176760776057456777188673317)
          ·
            refine ⟨33142645510773145722876247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176760776057456777188673317 33142645510773145722876247)
            ·
              refine ⟨49713968266159718584314371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33142645510773145722876247 49713968266159718584314371)
              ·
                refine ⟨74570952399239577876471557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49713968266159718584314371 74570952399239577876471557)
                ·
                  refine ⟨13982053574857420851838417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74570952399239577876471557 13982053574857420851838417)
                  ·
                    refine ⟨10486540181143065638878813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13982053574857420851838417 10486540181143065638878813)
                    ·
                      refine ⟨3932452567928649614579555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10486540181143065638878813 3932452567928649614579555)
                      ·
                        rfl

theorem cell23_7658424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_7658424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658424 prefixEnd_7658424 := by exact prefixLift 7658424
  have htrace : WordTrace (prefixWord ++ tailWord_7658424) baseStart_7658424 baseEnd_7658424 := by
    simpa [prefixWord, tailWord_7658424, baseEnd_7658424] using wordTrace_append hprefix tailTrace_7658424
  have hstable : (prefixWord ++ tailWord_7658424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658424).length < 2 ^ (prefixWord ++ tailWord_7658424).sum := by decide
  have hdescent : baseEnd_7658424 < baseStart_7658424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658444 : List Nat := [2, 2, 1, 4, 1, 1, 3, 3, 6]
def baseStart_7658444 : Nat := 118140960795 + 7658444 * 2 ^ 59
def prefixEnd_7658444 : Nat := 4983230072969 + 3 ^ 40 * 7658444 * 2
def baseEnd_7658444 : Nat := 436940315282415504036607

theorem tailTrace_7658444 : CollatzResearch.WordTrace tailWord_7658444 prefixEnd_7658444 436940315282415504036607 := by
  unfold tailWord_7658444
  simp only [CollatzResearch.WordTrace]
  refine ⟨139663200133386410474223193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186217600177848547298964257 139663200133386410474223193)
  ·
    refine ⟨104747400100039807855667395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139663200133386410474223193 104747400100039807855667395)
    ·
      refine ⟨157121100150059711783501093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104747400100039807855667395 157121100150059711783501093)
      ·
        refine ⟨29460206278136195959406455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157121100150059711783501093 29460206278136195959406455)
        ·
          refine ⟨44190309417204293939109683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29460206278136195959406455 44190309417204293939109683)
          ·
            refine ⟨66285464125806440908664525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44190309417204293939109683 66285464125806440908664525)
            ·
              refine ⟨24857049047177415340749197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66285464125806440908664525 24857049047177415340749197)
              ·
                refine ⟨9321393392691530752780949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24857049047177415340749197 9321393392691530752780949)
                ·
                  refine ⟨436940315282415504036607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9321393392691530752780949 436940315282415504036607)
                  ·
                    rfl

theorem cell23_7658444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 6].length) (baseStart_7658444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658444 prefixEnd_7658444 := by exact prefixLift 7658444
  have htrace : WordTrace (prefixWord ++ tailWord_7658444) baseStart_7658444 baseEnd_7658444 := by
    simpa [prefixWord, tailWord_7658444, baseEnd_7658444] using wordTrace_append hprefix tailTrace_7658444
  have hstable : (prefixWord ++ tailWord_7658444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658444).length < 2 ^ (prefixWord ++ tailWord_7658444).sum := by decide
  have hdescent : baseEnd_7658444 < baseStart_7658444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658504 : List Nat := [2, 1, 3, 2, 1, 3, 1, 3, 1, 6]
def baseStart_7658504 : Nat := 118140960795 + 7658504 * 2 ^ 59
def prefixEnd_7658504 : Nat := 4983230072969 + 3 ^ 40 * 7658504 * 2
def baseEnd_7658504 : Nat := 1310831215460336433859729

theorem tailTrace_7658504 : CollatzResearch.WordTrace tailWord_7658504 prefixEnd_7658504 1310831215460336433859729 := by
  unfold tailWord_7658504
  simp only [CollatzResearch.WordTrace]
  refine ⟨139664294323277725597815283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186219059097703634130420377 139664294323277725597815283)
  ·
    refine ⟨209496441484916588396722925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139664294323277725597815283 209496441484916588396722925)
    ·
      refine ⟨78561165556843720648771097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209496441484916588396722925 78561165556843720648771097)
      ·
        refine ⟨58920874167632790486578323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78561165556843720648771097 58920874167632790486578323)
        ·
          refine ⟨88381311251449185729867485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58920874167632790486578323 88381311251449185729867485)
          ·
            refine ⟨33142991719293444648700307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88381311251449185729867485 33142991719293444648700307)
            ·
              refine ⟨49714487578940166973050461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33142991719293444648700307 49714487578940166973050461)
              ·
                refine ⟨18642932842102562614893923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49714487578940166973050461 18642932842102562614893923)
                ·
                  refine ⟨27964399263153843922340885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18642932842102562614893923 27964399263153843922340885)
                  ·
                    refine ⟨1310831215460336433859729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27964399263153843922340885 1310831215460336433859729)
                    ·
                      rfl

theorem cell23_7658504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_7658504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658504 prefixEnd_7658504 := by exact prefixLift 7658504
  have htrace : WordTrace (prefixWord ++ tailWord_7658504) baseStart_7658504 baseEnd_7658504 := by
    simpa [prefixWord, tailWord_7658504, baseEnd_7658504] using wordTrace_append hprefix tailTrace_7658504
  have hstable : (prefixWord ++ tailWord_7658504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658504).length < 2 ^ (prefixWord ++ tailWord_7658504).sum := by decide
  have hdescent : baseEnd_7658504 < baseStart_7658504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658525 : List Nat := [1, 4, 2, 2, 3, 2, 2, 1, 1, 5]
def baseStart_7658525 : Nat := 118140960795 + 7658525 * 2 ^ 59
def prefixEnd_7658525 : Nat := 4983230072969 + 3 ^ 40 * 7658525 * 2
def baseEnd_7658525 : Nat := 1310834809824917906472197

theorem tailTrace_7658525 : CollatzResearch.WordTrace tailWord_7658525 prefixEnd_7658525 1310834809824917906472197 := by
  unfold tailWord_7658525
  simp only [CollatzResearch.WordTrace]
  refine ⟨279329354579479371782145029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186219569719652914521430019 279329354579479371782145029)
  ·
    refine ⟨52374253983652382209152193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279329354579479371782145029 52374253983652382209152193)
    ·
      refine ⟨39280690487739286656864145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52374253983652382209152193 39280690487739286656864145)
      ·
        refine ⟨29460517865804464992648109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39280690487739286656864145 29460517865804464992648109)
        ·
          refine ⟨11047694199676674372243041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29460517865804464992648109 11047694199676674372243041)
          ·
            refine ⟨8285770649757505779182281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11047694199676674372243041 8285770649757505779182281)
            ·
              refine ⟨6214327987318129334386711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8285770649757505779182281 6214327987318129334386711)
              ·
                refine ⟨9321491980977194001580067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6214327987318129334386711 9321491980977194001580067)
                ·
                  refine ⟨13982237971465791002370101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9321491980977194001580067 13982237971465791002370101)
                  ·
                    refine ⟨1310834809824917906472197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13982237971465791002370101 1310834809824917906472197)
                    ·
                      rfl

theorem cell23_7658525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_7658525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658525 prefixEnd_7658525 := by exact prefixLift 7658525
  have htrace : WordTrace (prefixWord ++ tailWord_7658525) baseStart_7658525 baseEnd_7658525 := by
    simpa [prefixWord, tailWord_7658525, baseEnd_7658525] using wordTrace_append hprefix tailTrace_7658525
  have hstable : (prefixWord ++ tailWord_7658525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658525).length < 2 ^ (prefixWord ++ tailWord_7658525).sum := by decide
  have hdescent : baseEnd_7658525 < baseStart_7658525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658538 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 4, 4]
def baseStart_7658538 : Nat := 118140960795 + 7658538 * 2 ^ 59
def prefixEnd_7658538 : Nat := 4983230072969 + 3 ^ 40 * 7658538 * 2
def baseEnd_7658538 : Nat := 1310837034907754056184677

theorem tailTrace_7658538 : CollatzResearch.WordTrace tailWord_7658538 prefixEnd_7658538 1310837034907754056184677 := by
  unfold tailWord_7658538
  simp only [CollatzResearch.WordTrace]
  refine ⟨69832457182108068750592067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186219885818954850001578845 69832457182108068750592067)
  ·
    refine ⟨104748685773162103125888101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69832457182108068750592067 104748685773162103125888101)
    ·
      refine ⟨19640378582467894336104019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104748685773162103125888101 19640378582467894336104019)
      ·
        refine ⟨29460567873701841504156029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19640378582467894336104019 29460567873701841504156029)
        ·
          refine ⟨11047712952638190564058511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29460567873701841504156029 11047712952638190564058511)
          ·
            refine ⟨16571569428957285846087767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11047712952638190564058511 16571569428957285846087767)
            ·
              refine ⟨24857354143435928769131651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16571569428957285846087767 24857354143435928769131651)
              ·
                refine ⟨37286031215153893153697477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24857354143435928769131651 37286031215153893153697477)
                ·
                  refine ⟨6991130852841354966318277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37286031215153893153697477 6991130852841354966318277)
                  ·
                    refine ⟨1310837034907754056184677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6991130852841354966318277 1310837034907754056184677)
                    ·
                      rfl

theorem cell23_7658538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_7658538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658538 prefixEnd_7658538 := by exact prefixLift 7658538
  have htrace : WordTrace (prefixWord ++ tailWord_7658538) baseStart_7658538 baseEnd_7658538 := by
    simpa [prefixWord, tailWord_7658538, baseEnd_7658538] using wordTrace_append hprefix tailTrace_7658538
  have hstable : (prefixWord ++ tailWord_7658538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658538).length < 2 ^ (prefixWord ++ tailWord_7658538).sum := by decide
  have hdescent : baseEnd_7658538 < baseStart_7658538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658545 : List Nat := [1, 2, 2, 3, 1, 2, 1, 6, 1, 2, 2]
def baseStart_7658545 : Nat := 118140960795 + 7658545 * 2 ^ 59
def prefixEnd_7658545 : Nat := 4983230072969 + 3 ^ 40 * 7658545 * 2
def baseEnd_7658545 : Nat := 3932514699087843641166499

theorem tailTrace_7658545 : CollatzResearch.WordTrace tailWord_7658545 prefixEnd_7658545 3932514699087843641166499 := by
  unfold tailWord_7658545
  simp only [CollatzResearch.WordTrace]
  refine ⟨279330084039406915197873089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186220056026271276798582059 279330084039406915197873089)
  ·
    refine ⟨209497563029555186398404817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279330084039406915197873089 209497563029555186398404817)
    ·
      refine ⟨157123172272166389798803613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209497563029555186398404817 157123172272166389798803613)
      ·
        refine ⟨58921189602062396174551355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157123172272166389798803613 58921189602062396174551355)
        ·
          refine ⟨88381784403093594261827033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58921189602062396174551355 88381784403093594261827033)
          ·
            refine ⟨66286338302320195696370275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88381784403093594261827033 66286338302320195696370275)
            ·
              refine ⟨99429507453480293544555413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66286338302320195696370275 99429507453480293544555413)
              ·
                refine ⟨4660758161881888759901035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99429507453480293544555413 4660758161881888759901035)
                ·
                  refine ⟨6991137242822833139851553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4660758161881888759901035 6991137242822833139851553)
                  ·
                    refine ⟨5243352932117124854888665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6991137242822833139851553 5243352932117124854888665)
                    ·
                      refine ⟨3932514699087843641166499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5243352932117124854888665 3932514699087843641166499)
                      ·
                        rfl

theorem cell23_7658545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_7658545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658545 prefixEnd_7658545 := by exact prefixLift 7658545
  have htrace : WordTrace (prefixWord ++ tailWord_7658545) baseStart_7658545 baseEnd_7658545 := by
    simpa [prefixWord, tailWord_7658545, baseEnd_7658545] using wordTrace_append hprefix tailTrace_7658545
  have hstable : (prefixWord ++ tailWord_7658545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658545).length < 2 ^ (prefixWord ++ tailWord_7658545).sum := by decide
  have hdescent : baseEnd_7658545 < baseStart_7658545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658548 : List Nat := [2, 5, 1, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_7658548 : Nat := 118140960795 + 7658548 * 2 ^ 59
def prefixEnd_7658548 : Nat := 4983230072969 + 3 ^ 40 * 7658548 * 2
def baseEnd_7658548 : Nat := 3932516239529807129428985

theorem tailTrace_7658548 : CollatzResearch.WordTrace tailWord_7658548 prefixEnd_7658548 3932516239529807129428985 := by
  unfold tailWord_7658548
  simp only [CollatzResearch.WordTrace]
  refine ⟨139665096729198023355116149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186220128972264031140154865 139665096729198023355116149)
  ·
    refine ⟨13093602818362314689542139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139665096729198023355116149 13093602818362314689542139)
    ·
      refine ⟨19640404227543472034313209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13093602818362314689542139 19640404227543472034313209)
      ·
        refine ⟨14730303170657604025734907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19640404227543472034313209 14730303170657604025734907)
        ·
          refine ⟨22095454755986406038602361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14730303170657604025734907 22095454755986406038602361)
          ·
            refine ⟨16571591066989804528951771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22095454755986406038602361 16571591066989804528951771)
            ·
              refine ⟨24857386600484706793427657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16571591066989804528951771 24857386600484706793427657)
              ·
                refine ⟨18643039950363530095070743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24857386600484706793427657 18643039950363530095070743)
                ·
                  refine ⟨27964559925545295142606115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18643039950363530095070743 27964559925545295142606115)
                  ·
                    refine ⟨41946839888317942713909173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27964559925545295142606115 41946839888317942713909173)
                    ·
                      refine ⟨3932516239529807129428985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41946839888317942713909173 3932516239529807129428985)
                      ·
                        rfl

theorem cell23_7658548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_7658548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658548 prefixEnd_7658548 := by exact prefixLift 7658548
  have htrace : WordTrace (prefixWord ++ tailWord_7658548) baseStart_7658548 baseEnd_7658548 := by
    simpa [prefixWord, tailWord_7658548, baseEnd_7658548] using wordTrace_append hprefix tailTrace_7658548
  have hstable : (prefixWord ++ tailWord_7658548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658548).length < 2 ^ (prefixWord ++ tailWord_7658548).sum := by decide
  have hdescent : baseEnd_7658548 < baseStart_7658548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658558 : List Nat := [4, 2, 1, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_7658558 : Nat := 118140960795 + 7658558 * 2 ^ 59
def prefixEnd_7658558 : Nat := 4983230072969 + 3 ^ 40 * 7658558 * 2
def baseEnd_7658558 : Nat := 3932521374336352090303939

theorem tailTrace_7658558 : CollatzResearch.WordTrace tailWord_7658558 prefixEnd_7658558 3932521374336352090303939 := by
  unfold tailWord_7658558
  simp only [CollatzResearch.WordTrace]
  refine ⟨34916319773544977302262041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186220372125573212278730885 34916319773544977302262041)
  ·
    refine ⟨26187239830158732976696531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34916319773544977302262041 26187239830158732976696531)
    ·
      refine ⟨39280859745238099465044797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26187239830158732976696531 39280859745238099465044797)
      ·
        refine ⟨14730322404464287299391799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39280859745238099465044797 14730322404464287299391799)
        ·
          refine ⟨22095483606696430949087699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14730322404464287299391799 22095483606696430949087699)
          ·
            refine ⟨33143225410044646423631549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22095483606696430949087699 33143225410044646423631549)
            ·
              refine ⟨12428709528766742408861831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33143225410044646423631549 12428709528766742408861831)
              ·
                refine ⟨18643064293150113613292747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12428709528766742408861831 18643064293150113613292747)
                ·
                  refine ⟨27964596439725170419939121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18643064293150113613292747 27964596439725170419939121)
                  ·
                    refine ⟨20973447329793877814954341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27964596439725170419939121 20973447329793877814954341)
                    ·
                      refine ⟨3932521374336352090303939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20973447329793877814954341 3932521374336352090303939)
                      ·
                        rfl

theorem cell23_7658558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_7658558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658558 prefixEnd_7658558 := by exact prefixLift 7658558
  have htrace : WordTrace (prefixWord ++ tailWord_7658558) baseStart_7658558 baseEnd_7658558 := by
    simpa [prefixWord, tailWord_7658558, baseEnd_7658558] using wordTrace_append hprefix tailTrace_7658558
  have hstable : (prefixWord ++ tailWord_7658558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658558).length < 2 ^ (prefixWord ++ tailWord_7658558).sum := by decide
  have hdescent : baseEnd_7658558 < baseStart_7658558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658574 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_7658574 : Nat := 118140960795 + 7658574 * 2 ^ 59
def prefixEnd_7658574 : Nat := 4983230072969 + 3 ^ 40 * 7658574 * 2
def baseEnd_7658574 : Nat := 3932529590026824027703865

theorem tailTrace_7658574 : CollatzResearch.WordTrace tailWord_7658574 prefixEnd_7658574 3932529590026824027703865 := by
  unfold tailWord_7658574
  simp only [CollatzResearch.WordTrace]
  refine ⟨34916392719537731643834847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186220761170867902100452517 34916392719537731643834847)
  ·
    refine ⟨52374589079306597465752271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34916392719537731643834847 52374589079306597465752271)
    ·
      refine ⟨78561883618959896198628407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52374589079306597465752271 78561883618959896198628407)
      ·
        refine ⟨117842825428439844297942611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78561883618959896198628407 117842825428439844297942611)
        ·
          refine ⟨176764238142659766446913917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117842825428439844297942611 176764238142659766446913917)
          ·
            refine ⟨66286589303497412417592719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176764238142659766446913917 66286589303497412417592719)
            ·
              refine ⟨99429883955246118626389079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66286589303497412417592719 99429883955246118626389079)
              ·
                refine ⟨149144825932869177939583619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99429883955246118626389079 149144825932869177939583619)
                ·
                  refine ⟨223717238899303766909375429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149144825932869177939583619 223717238899303766909375429)
                  ·
                    refine ⟨41946982293619456295507893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 223717238899303766909375429 41946982293619456295507893)
                    ·
                      refine ⟨3932529590026824027703865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41946982293619456295507893 3932529590026824027703865)
                      ·
                        rfl

theorem cell23_7658574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_7658574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658574 prefixEnd_7658574 := by exact prefixLift 7658574
  have htrace : WordTrace (prefixWord ++ tailWord_7658574) baseStart_7658574 baseEnd_7658574 := by
    simpa [prefixWord, tailWord_7658574, baseEnd_7658574] using wordTrace_append hprefix tailTrace_7658574
  have hstable : (prefixWord ++ tailWord_7658574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658574).length < 2 ^ (prefixWord ++ tailWord_7658574).sum := by decide
  have hdescent : baseEnd_7658574 < baseStart_7658574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658578 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_7658578 : Nat := 118140960795 + 7658578 * 2 ^ 59
def prefixEnd_7658578 : Nat := 4983230072969 + 3 ^ 40 * 7658578 * 2
def baseEnd_7658578 : Nat := 3932531643949442012053847

theorem tailTrace_7658578 : CollatzResearch.WordTrace tailWord_7658578 prefixEnd_7658578 3932531643949442012053847 := by
  unfold tailWord_7658578
  simp only [CollatzResearch.WordTrace]
  refine ⟨69832821912071840458456097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186220858432191574555882925 69832821912071840458456097)
  ·
    refine ⟨52374616434053880343842073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69832821912071840458456097 52374616434053880343842073)
    ·
      refine ⟨39280962325540410257881555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52374616434053880343842073 39280962325540410257881555)
      ·
        refine ⟨58921443488310615386822333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39280962325540410257881555 58921443488310615386822333)
        ·
          refine ⟨22095541308116480770058375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58921443488310615386822333 22095541308116480770058375)
          ·
            refine ⟨33143311962174721155087563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22095541308116480770058375 33143311962174721155087563)
            ·
              refine ⟨49714967943262081732631345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33143311962174721155087563 49714967943262081732631345)
              ·
                refine ⟨37286225957446561299473509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49714967943262081732631345 37286225957446561299473509)
                ·
                  refine ⟨6991167367021230243651283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37286225957446561299473509 6991167367021230243651283)
                  ·
                    refine ⟨10486751050531845365476925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6991167367021230243651283 10486751050531845365476925)
                    ·
                      refine ⟨3932531643949442012053847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10486751050531845365476925 3932531643949442012053847)
                      ·
                        rfl

theorem cell23_7658578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_7658578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658578 prefixEnd_7658578 := by exact prefixLift 7658578
  have htrace : WordTrace (prefixWord ++ tailWord_7658578) baseStart_7658578 baseEnd_7658578 := by
    simpa [prefixWord, tailWord_7658578, baseEnd_7658578] using wordTrace_append hprefix tailTrace_7658578
  have hstable : (prefixWord ++ tailWord_7658578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658578).length < 2 ^ (prefixWord ++ tailWord_7658578).sum := by decide
  have hdescent : baseEnd_7658578 < baseStart_7658578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658604 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 5]
def baseStart_7658604 : Nat := 118140960795 + 7658604 * 2 ^ 59
def prefixEnd_7658604 : Nat := 4983230072969 + 3 ^ 40 * 7658604 * 2
def baseEnd_7658604 : Nat := 3932544994446458910328727

theorem tailTrace_7658604 : CollatzResearch.WordTrace tailWord_7658604 prefixEnd_7658604 3932544994446458910328727 := by
  unfold tailWord_7658604
  simp only [CollatzResearch.WordTrace]
  refine ⟨139666117973096584137135433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186221490630795445516180577 139666117973096584137135433)
  ·
    refine ⟨104749588479822438102851575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139666117973096584137135433 104749588479822438102851575)
    ·
      refine ⟨157124382719733657154277363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104749588479822438102851575 157124382719733657154277363)
      ·
        refine ⟨235686574079600485731416045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157124382719733657154277363 235686574079600485731416045)
        ·
          refine ⟨88382465279850182149281017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235686574079600485731416045 88382465279850182149281017)
          ·
            refine ⟨66286848959887636611960763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88382465279850182149281017 66286848959887636611960763)
            ·
              refine ⟨99430273439831454917941145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66286848959887636611960763 99430273439831454917941145)
              ·
                refine ⟨74572705079873591188455859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99430273439831454917941145 74572705079873591188455859)
                ·
                  refine ⟨111859057619810386782683789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74572705079873591188455859 111859057619810386782683789)
                  ·
                    refine ⟨41947146607428895043506421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111859057619810386782683789 41947146607428895043506421)
                    ·
                      refine ⟨3932544994446458910328727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41947146607428895043506421 3932544994446458910328727)
                      ·
                        rfl

theorem cell23_7658604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_7658604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658604 prefixEnd_7658604 := by exact prefixLift 7658604
  have htrace : WordTrace (prefixWord ++ tailWord_7658604) baseStart_7658604 baseEnd_7658604 := by
    simpa [prefixWord, tailWord_7658604, baseEnd_7658604] using wordTrace_append hprefix tailTrace_7658604
  have hstable : (prefixWord ++ tailWord_7658604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658604).length < 2 ^ (prefixWord ++ tailWord_7658604).sum := by decide
  have hdescent : baseEnd_7658604 < baseStart_7658604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658624 : List Nat := [2, 1, 1, 2, 1, 3, 2, 4, 7]
def baseStart_7658624 : Nat := 118140960795 + 7658624 * 2 ^ 59
def prefixEnd_7658624 : Nat := 4983230072969 + 3 ^ 40 * 7658624 * 2
def baseEnd_7658624 : Nat := 436950584895505425786515

theorem tailTrace_7658624 : CollatzResearch.WordTrace tailWord_7658624 prefixEnd_7658624 436950584895505425786515 := by
  unfold tailWord_7658624
  simp only [CollatzResearch.WordTrace]
  refine ⟨139666482703060355844999463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186221976937413807793332617 139666482703060355844999463)
  ·
    refine ⟨209499724054590533767499195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139666482703060355844999463 209499724054590533767499195)
    ·
      refine ⟨314249586081885800651248793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209499724054590533767499195 314249586081885800651248793)
      ·
        refine ⟨235687189561414350488436595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314249586081885800651248793 235687189561414350488436595)
        ·
          refine ⟨353530784342121525732654893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235687189561414350488436595 353530784342121525732654893)
          ·
            refine ⟨132574044128295572149745585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353530784342121525732654893 132574044128295572149745585)
            ·
              refine ⟨99430533096221679112309189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132574044128295572149745585 99430533096221679112309189)
              ·
                refine ⟨18643224955541564833557973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99430533096221679112309189 18643224955541564833557973)
                ·
                  refine ⟨436950584895505425786515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18643224955541564833557973 436950584895505425786515)
                  ·
                    rfl

theorem cell23_7658624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 7].length) (baseStart_7658624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658624 prefixEnd_7658624 := by exact prefixLift 7658624
  have htrace : WordTrace (prefixWord ++ tailWord_7658624) baseStart_7658624 baseEnd_7658624 := by
    simpa [prefixWord, tailWord_7658624, baseEnd_7658624] using wordTrace_append hprefix tailTrace_7658624
  have hstable : (prefixWord ++ tailWord_7658624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658624).length < 2 ^ (prefixWord ++ tailWord_7658624).sum := by decide
  have hdescent : baseEnd_7658624 < baseStart_7658624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658652 : List Nat := [2, 2, 3, 2, 1, 3, 2, 2, 2, 2, 2]
def baseStart_7658652 : Nat := 118140960795 + 7658652 * 2 ^ 59
def prefixEnd_7658652 : Nat := 4983230072969 + 3 ^ 40 * 7658652 * 2
def baseEnd_7658652 : Nat := 3932569641517874722528507

theorem tailTrace_7658652 : CollatzResearch.WordTrace tailWord_7658652 prefixEnd_7658652 3932569641517874722528507 := by
  unfold tailWord_7658652
  simp only [CollatzResearch.WordTrace]
  refine ⟨139666993325009636236009105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186222657766679514981345473 139666993325009636236009105)
  ·
    refine ⟨104750244993757227177006829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139666993325009636236009105 104750244993757227177006829)
    ·
      refine ⟨39281341872658960191377561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104750244993757227177006829 39281341872658960191377561)
      ·
        refine ⟨29461006404494220143533171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39281341872658960191377561 29461006404494220143533171)
        ·
          refine ⟨44191509606741330215299757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29461006404494220143533171 44191509606741330215299757)
          ·
            refine ⟨16571816102527998830737409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44191509606741330215299757 16571816102527998830737409)
            ·
              refine ⟨12428862076895999123053057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16571816102527998830737409 12428862076895999123053057)
              ·
                refine ⟨9321646557671999342289793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12428862076895999123053057 9321646557671999342289793)
                ·
                  refine ⟨6991234918253999506717345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9321646557671999342289793 6991234918253999506717345)
                  ·
                    refine ⟨5243426188690499630038009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6991234918253999506717345 5243426188690499630038009)
                    ·
                      refine ⟨3932569641517874722528507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5243426188690499630038009 3932569641517874722528507)
                      ·
                        rfl

theorem cell23_7658652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_7658652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658652 prefixEnd_7658652 := by exact prefixLift 7658652
  have htrace : WordTrace (prefixWord ++ tailWord_7658652) baseStart_7658652 baseEnd_7658652 := by
    simpa [prefixWord, tailWord_7658652, baseEnd_7658652] using wordTrace_append hprefix tailTrace_7658652
  have hstable : (prefixWord ++ tailWord_7658652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658652).length < 2 ^ (prefixWord ++ tailWord_7658652).sum := by decide
  have hdescent : baseEnd_7658652 < baseStart_7658652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658691 : List Nat := [1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 4]
def baseStart_7658691 : Nat := 118140960795 + 7658691 * 2 ^ 59
def prefixEnd_7658691 : Nat := 4983230072969 + 3 ^ 40 * 7658691 * 2
def baseEnd_7658691 : Nat := 3932589667263400069940827

theorem tailTrace_7658691 : CollatzResearch.WordTrace tailWord_7658691 prefixEnd_7658691 3932589667263400069940827 := by
  unfold tailWord_7658691
  simp only [CollatzResearch.WordTrace]
  refine ⟨279335409096877982132687927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186223606064585321421791951 279335409096877982132687927)
  ·
    refine ⟨419003113645316973199031891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279335409096877982132687927 419003113645316973199031891)
    ·
      refine ⟨628504670467975459798547837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419003113645316973199031891 628504670467975459798547837)
      ·
        refine ⟨235689251425490797424455439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 628504670467975459798547837 235689251425490797424455439)
        ·
          refine ⟨353533877138236196136683159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235689251425490797424455439 353533877138236196136683159)
          ·
            refine ⟨530300815707354294205024739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353533877138236196136683159 530300815707354294205024739)
            ·
              refine ⟨795451223561031441307537109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530300815707354294205024739 795451223561031441307537109)
              ·
                refine ⟨18643388052211674405645401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 795451223561031441307537109 18643388052211674405645401)
                ·
                  refine ⟨13982541039158755804234051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18643388052211674405645401 13982541039158755804234051)
                  ·
                    refine ⟨20973811558738133706351077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13982541039158755804234051 20973811558738133706351077)
                    ·
                      refine ⟨3932589667263400069940827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20973811558738133706351077 3932589667263400069940827)
                      ·
                        rfl

theorem cell23_7658691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_7658691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658691 prefixEnd_7658691 := by exact prefixLift 7658691
  have htrace : WordTrace (prefixWord ++ tailWord_7658691) baseStart_7658691 baseEnd_7658691 := by
    simpa [prefixWord, tailWord_7658691, baseEnd_7658691] using wordTrace_append hprefix tailTrace_7658691
  have hstable : (prefixWord ++ tailWord_7658691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658691).length < 2 ^ (prefixWord ++ tailWord_7658691).sum := by decide
  have hdescent : baseEnd_7658691 < baseStart_7658691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658782 : List Nat := [4, 3, 2, 1, 2, 1, 1, 3, 6]
def baseStart_7658782 : Nat := 118140960795 + 7658782 * 2 ^ 59
def prefixEnd_7658782 : Nat := 4983230072969 + 3 ^ 40 * 7658782 * 2
def baseEnd_7658782 : Nat := 436959599333662134878101

theorem tailTrace_7658782 : CollatzResearch.WordTrace tailWord_7658782 prefixEnd_7658782 436959599333662134878101 := by
  unfold tailWord_7658782
  simp only [CollatzResearch.WordTrace]
  refine ⟨34917341017443538084281325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186225818759698869782833733 34917341017443538084281325)
  ·
    refine ⟨13094002881541326781605497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34917341017443538084281325 13094002881541326781605497)
    ·
      refine ⟨9820502161155995086204123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13094002881541326781605497 9820502161155995086204123)
      ·
        refine ⟨14730753241733992629306185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9820502161155995086204123 14730753241733992629306185)
        ·
          refine ⟨11048064931300494471979639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14730753241733992629306185 11048064931300494471979639)
          ·
            refine ⟨16572097396950741707969459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11048064931300494471979639 16572097396950741707969459)
            ·
              refine ⟨24858146095426112561954189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16572097396950741707969459 24858146095426112561954189)
              ·
                refine ⟨9321804785784792210732821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24858146095426112561954189 9321804785784792210732821)
                ·
                  refine ⟨436959599333662134878101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9321804785784792210732821 436959599333662134878101)
                  ·
                    rfl

theorem cell23_7658782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_7658782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658782 prefixEnd_7658782 := by exact prefixLift 7658782
  have htrace : WordTrace (prefixWord ++ tailWord_7658782) baseStart_7658782 baseEnd_7658782 := by
    simpa [prefixWord, tailWord_7658782, baseEnd_7658782] using wordTrace_append hprefix tailTrace_7658782
  have hstable : (prefixWord ++ tailWord_7658782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658782).length < 2 ^ (prefixWord ++ tailWord_7658782).sum := by decide
  have hdescent : baseEnd_7658782 < baseStart_7658782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658802 : List Nat := [3, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2]
def baseStart_7658802 : Nat := 118140960795 + 7658802 * 2 ^ 59
def prefixEnd_7658802 : Nat := 4983230072969 + 3 ^ 40 * 7658802 * 2
def baseEnd_7658802 : Nat := 3932646663616049135652817

theorem tailTrace_7658802 : CollatzResearch.WordTrace tailWord_7658802 prefixEnd_7658802 3932646663616049135652817 := by
  unfold tailWord_7658802
  simp only [CollatzResearch.WordTrace]
  refine ⟨69834864399868962022494665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186226305066317232059985773 69834864399868962022494665)
  ·
    refine ⟨52376148299901721516870999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69834864399868962022494665 52376148299901721516870999)
    ·
      refine ⟨78564222449852582275306499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52376148299901721516870999 78564222449852582275306499)
      ·
        refine ⟨117846333674778873412959749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78564222449852582275306499 117846333674778873412959749)
        ·
          refine ⟨22096187564021038764929953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117846333674778873412959749 22096187564021038764929953)
          ·
            refine ⟨16572140673015779073697465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22096187564021038764929953 16572140673015779073697465)
            ·
              refine ⟨12429105504761834305273099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16572140673015779073697465 12429105504761834305273099)
              ·
                refine ⟨18643658257142751457909649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12429105504761834305273099 18643658257142751457909649)
                ·
                  refine ⟨13982743692857063593432237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18643658257142751457909649 13982743692857063593432237)
                  ·
                    refine ⟨5243528884821398847537089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13982743692857063593432237 5243528884821398847537089)
                    ·
                      refine ⟨3932646663616049135652817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5243528884821398847537089 3932646663616049135652817)
                      ·
                        rfl

theorem cell23_7658802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_7658802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658802 prefixEnd_7658802 := by exact prefixLift 7658802
  have htrace : WordTrace (prefixWord ++ tailWord_7658802) baseStart_7658802 baseEnd_7658802 := by
    simpa [prefixWord, tailWord_7658802, baseEnd_7658802] using wordTrace_append hprefix tailTrace_7658802
  have hstable : (prefixWord ++ tailWord_7658802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658802).length < 2 ^ (prefixWord ++ tailWord_7658802).sum := by decide
  have hdescent : baseEnd_7658802 < baseStart_7658802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658841 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 6]
def baseStart_7658841 : Nat := 118140960795 + 7658841 * 2 ^ 59
def prefixEnd_7658841 : Nat := 4983230072969 + 3 ^ 40 * 7658841 * 2
def baseEnd_7658841 : Nat := 3932666689361574483065137

theorem tailTrace_7658841 : CollatzResearch.WordTrace tailWord_7658841 prefixEnd_7658841 3932666689361574483065137 := by
  unfold tailWord_7658841
  simp only [CollatzResearch.WordTrace]
  refine ⟨279340880046334557750648377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186227253364223038500432251 279340880046334557750648377)
  ·
    refine ⟨209505660034750918312986283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279340880046334557750648377 209505660034750918312986283)
    ·
      refine ⟨314258490052126377469479425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209505660034750918312986283 314258490052126377469479425)
      ·
        refine ⟨235693867539094783102109569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314258490052126377469479425 235693867539094783102109569)
        ·
          refine ⟨176770400654321087326582177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235693867539094783102109569 176770400654321087326582177)
          ·
            refine ⟨132577800490740815494936633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176770400654321087326582177 132577800490740815494936633)
            ·
              refine ⟨99433350368055611621202475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132577800490740815494936633 99433350368055611621202475)
              ·
                refine ⟨149150025552083417431803713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99433350368055611621202475 149150025552083417431803713)
                ·
                  refine ⟨111862519164062563073852785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149150025552083417431803713 111862519164062563073852785)
                  ·
                    refine ⟨83896889373046922305389589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111862519164062563073852785 83896889373046922305389589)
                    ·
                      refine ⟨3932666689361574483065137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83896889373046922305389589 3932666689361574483065137)
                      ·
                        rfl

theorem cell23_7658841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_7658841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658841 prefixEnd_7658841 := by exact prefixLift 7658841
  have htrace : WordTrace (prefixWord ++ tailWord_7658841) baseStart_7658841 baseEnd_7658841 := by
    simpa [prefixWord, tailWord_7658841, baseEnd_7658841] using wordTrace_append hprefix tailTrace_7658841
  have hstable : (prefixWord ++ tailWord_7658841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658841).length < 2 ^ (prefixWord ++ tailWord_7658841).sum := by decide
  have hdescent : baseEnd_7658841 < baseStart_7658841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658855 : List Nat := [1, 1, 5, 1, 4, 1, 3, 7]
def baseStart_7658855 : Nat := 118140960795 + 7658855 * 2 ^ 59
def prefixEnd_7658855 : Nat := 4983230072969 + 3 ^ 40 * 7658855 * 2
def baseEnd_7658855 : Nat := 145654588077434719566299

theorem tailTrace_7658855 : CollatzResearch.WordTrace tailWord_7658855 prefixEnd_7658855 145654588077434719566299 := by
  unfold tailWord_7658855
  simp only [CollatzResearch.WordTrace]
  refine ⟨279341390668283838141658019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186227593778855892094438679 279341390668283838141658019)
  ·
    refine ⟨419012086002425757212487029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279341390668283838141658019 419012086002425757212487029)
    ·
      refine ⟨39282383062727414738670659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 419012086002425757212487029 39282383062727414738670659)
      ·
        refine ⟨58923574594091122108005989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39282383062727414738670659 58923574594091122108005989)
        ·
          refine ⟨11048170236392085395251123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58923574594091122108005989 11048170236392085395251123)
          ·
            refine ⟨16572255354588128092876685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11048170236392085395251123 16572255354588128092876685)
            ·
              refine ⟨6214595757970548034828757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16572255354588128092876685 6214595757970548034828757)
              ·
                refine ⟨145654588077434719566299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6214595757970548034828757 145654588077434719566299)
                ·
                  rfl

theorem cell23_7658855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 7].length) (baseStart_7658855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658855 prefixEnd_7658855 := by exact prefixLift 7658855
  have htrace : WordTrace (prefixWord ++ tailWord_7658855) baseStart_7658855 baseEnd_7658855 := by
    simpa [prefixWord, tailWord_7658855, baseEnd_7658855] using wordTrace_append hprefix tailTrace_7658855
  have hstable : (prefixWord ++ tailWord_7658855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658855).length < 2 ^ (prefixWord ++ tailWord_7658855).sum := by decide
  have hdescent : baseEnd_7658855 < baseStart_7658855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658909 : List Nat := [1, 4, 2, 1, 3, 2, 2, 2, 1, 3, 2]
def baseStart_7658909 : Nat := 118140960795 + 7658909 * 2 ^ 59
def prefixEnd_7658909 : Nat := 4983230072969 + 3 ^ 40 * 7658909 * 2
def baseEnd_7658909 : Nat := 3932701606046080217014825

theorem tailTrace_7658909 : CollatzResearch.WordTrace tailWord_7658909 prefixEnd_7658909 3932701606046080217014825 := by
  unfold tailWord_7658909
  simp only [CollatzResearch.WordTrace]
  refine ⟨279343360210088205364123781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186228906806725470242749187 279343360210088205364123781)
  ·
    refine ⟨52376880039391538505773209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279343360210088205364123781 52376880039391538505773209)
    ·
      refine ⟨39282660029543653879329907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52376880039391538505773209 39282660029543653879329907)
      ·
        refine ⟨58923990044315480818994861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39282660029543653879329907 58923990044315480818994861)
        ·
          refine ⟨22096496266618305307123073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58923990044315480818994861 22096496266618305307123073)
          ·
            refine ⟨16572372199963728980342305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22096496266618305307123073 16572372199963728980342305)
            ·
              refine ⟨12429279149972796735256729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16572372199963728980342305 12429279149972796735256729)
              ·
                refine ⟨9321959362479597551442547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12429279149972796735256729 9321959362479597551442547)
                ·
                  refine ⟨13982939043719396327163821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9321959362479597551442547 13982939043719396327163821)
                  ·
                    refine ⟨5243602141394773622686433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13982939043719396327163821 5243602141394773622686433)
                    ·
                      refine ⟨3932701606046080217014825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5243602141394773622686433 3932701606046080217014825)
                      ·
                        rfl

theorem cell23_7658909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_7658909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658909 prefixEnd_7658909 := by exact prefixLift 7658909
  have htrace : WordTrace (prefixWord ++ tailWord_7658909) baseStart_7658909 baseEnd_7658909 := by
    simpa [prefixWord, tailWord_7658909, baseEnd_7658909] using wordTrace_append hprefix tailTrace_7658909
  have hstable : (prefixWord ++ tailWord_7658909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658909).length < 2 ^ (prefixWord ++ tailWord_7658909).sum := by decide
  have hdescent : baseEnd_7658909 < baseStart_7658909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658925 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_7658925 : Nat := 118140960795 + 7658925 * 2 ^ 59
def prefixEnd_7658925 : Nat := 4983230072969 + 3 ^ 40 * 7658925 * 2
def baseEnd_7658925 : Nat := 3932709821736552154414751

theorem tailTrace_7658925 : CollatzResearch.WordTrace tailWord_7658925 prefixEnd_7658925 3932709821736552154414751 := by
  unfold tailWord_7658925
  simp only [CollatzResearch.WordTrace]
  refine ⟨279343943778030240096706229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186229295852020160064470819 279343943778030240096706229)
  ·
    refine ⟨26188494729190335009066209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279343943778030240096706229 26188494729190335009066209)
    ·
      refine ⟨19641371046892751256799657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26188494729190335009066209 19641371046892751256799657)
      ·
        refine ⟨14731028285169563442599743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19641371046892751256799657 14731028285169563442599743)
        ·
          refine ⟨22096542427754345163899615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14731028285169563442599743 22096542427754345163899615)
          ·
            refine ⟨33144813641631517745849423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22096542427754345163899615 33144813641631517745849423)
            ·
              refine ⟨49717220462447276618774135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33144813641631517745849423 49717220462447276618774135)
              ·
                refine ⟨74575830693670914928161203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49717220462447276618774135 74575830693670914928161203)
                ·
                  refine ⟨111863746040506372392241805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74575830693670914928161203 111863746040506372392241805)
                  ·
                    refine ⟨41948904765189889647090677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111863746040506372392241805 41948904765189889647090677)
                    ·
                      refine ⟨3932709821736552154414751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41948904765189889647090677 3932709821736552154414751)
                      ·
                        rfl

theorem cell23_7658925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_7658925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658925 prefixEnd_7658925 := by exact prefixLift 7658925
  have htrace : WordTrace (prefixWord ++ tailWord_7658925) baseStart_7658925 baseEnd_7658925 := by
    simpa [prefixWord, tailWord_7658925, baseEnd_7658925] using wordTrace_append hprefix tailTrace_7658925
  have hstable : (prefixWord ++ tailWord_7658925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658925).length < 2 ^ (prefixWord ++ tailWord_7658925).sum := by decide
  have hdescent : baseEnd_7658925 < baseStart_7658925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658956 : List Nat := [2, 2, 1, 4, 2, 1, 4, 1, 2, 2, 2]
def baseStart_7658956 : Nat := 118140960795 + 7658956 * 2 ^ 59
def prefixEnd_7658956 : Nat := 4983230072969 + 3 ^ 40 * 7658956 * 2
def baseEnd_7658956 : Nat := 3932725739636841533127109

theorem tailTrace_7658956 : CollatzResearch.WordTrace tailWord_7658956 prefixEnd_7658956 3932725739636841533127109 := by
  unfold tailWord_7658956
  simp only [CollatzResearch.WordTrace]
  refine ⟨139672537220458966195542361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186230049627278621594056481 139672537220458966195542361)
  ·
    refine ⟨104754402915344224646656771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139672537220458966195542361 104754402915344224646656771)
    ·
      refine ⟨157131604373016336969985157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104754402915344224646656771 157131604373016336969985157)
      ·
        refine ⟨29462175819940563181872217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157131604373016336969985157 29462175819940563181872217)
        ·
          refine ⟨22096631864955422386404163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29462175819940563181872217 22096631864955422386404163)
          ·
            refine ⟨33144947797433133579606245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22096631864955422386404163 33144947797433133579606245)
            ·
              refine ⟨6214677712018712546176171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33144947797433133579606245 6214677712018712546176171)
              ·
                refine ⟨9322016568028068819264257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6214677712018712546176171 9322016568028068819264257)
                ·
                  refine ⟨6991512426021051614448193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9322016568028068819264257 6991512426021051614448193)
                  ·
                    refine ⟨5243634319515788710836145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6991512426021051614448193 5243634319515788710836145)
                    ·
                      refine ⟨3932725739636841533127109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5243634319515788710836145 3932725739636841533127109)
                      ·
                        rfl

theorem cell23_7658956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_7658956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658956 prefixEnd_7658956 := by exact prefixLift 7658956
  have htrace : WordTrace (prefixWord ++ tailWord_7658956) baseStart_7658956 baseEnd_7658956 := by
    simpa [prefixWord, tailWord_7658956, baseEnd_7658956] using wordTrace_append hprefix tailTrace_7658956
  have hstable : (prefixWord ++ tailWord_7658956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658956).length < 2 ^ (prefixWord ++ tailWord_7658956).sum := by decide
  have hdescent : baseEnd_7658956 < baseStart_7658956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658958 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 3, 7]
def baseStart_7658958 : Nat := 118140960795 + 7658958 * 2 ^ 59
def prefixEnd_7658958 : Nat := 4983230072969 + 3 ^ 40 * 7658958 * 2
def baseEnd_7658958 : Nat := 1310908922199383508434033

theorem tailTrace_7658958 : CollatzResearch.WordTrace tailWord_7658958 prefixEnd_7658958 1310908922199383508434033 := by
  unfold tailWord_7658958
  simp only [CollatzResearch.WordTrace]
  refine ⟨34918143423363835841582191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186230098257940457821771685 34918143423363835841582191)
  ·
    refine ⟨52377215135045753762373287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34918143423363835841582191 52377215135045753762373287)
    ·
      refine ⟨78565822702568630643559931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52377215135045753762373287 78565822702568630643559931)
      ·
        refine ⟨117848734053852945965339897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78565822702568630643559931 117848734053852945965339897)
        ·
          refine ⟨88386550540389709474004923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117848734053852945965339897 88386550540389709474004923)
          ·
            refine ⟨132579825810584564211007385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88386550540389709474004923 132579825810584564211007385)
            ·
              refine ⟨99434869357938423158255539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132579825810584564211007385 99434869357938423158255539)
              ·
                refine ⟨149152304036907634737383309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99434869357938423158255539 149152304036907634737383309)
                ·
                  refine ⟨55932114013840363026518741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149152304036907634737383309 55932114013840363026518741)
                  ·
                    refine ⟨1310908922199383508434033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55932114013840363026518741 1310908922199383508434033)
                    ·
                      rfl

theorem cell23_7658958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_7658958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658958 prefixEnd_7658958 := by exact prefixLift 7658958
  have htrace : WordTrace (prefixWord ++ tailWord_7658958) baseStart_7658958 baseEnd_7658958 := by
    simpa [prefixWord, tailWord_7658958, baseEnd_7658958] using wordTrace_append hprefix tailTrace_7658958
  have hstable : (prefixWord ++ tailWord_7658958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658958).length < 2 ^ (prefixWord ++ tailWord_7658958).sum := by decide
  have hdescent : baseEnd_7658958 < baseStart_7658958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7658975 : List Nat := [1, 1, 2, 3, 3, 1, 4, 1, 2, 5]
def baseStart_7658975 : Nat := 118140960795 + 7658975 * 2 ^ 59
def prefixEnd_7658975 : Nat := 4983230072969 + 3 ^ 40 * 7658975 * 2
def baseEnd_7658975 : Nat := 1310911831923092319596507

theorem tailTrace_7658975 : CollatzResearch.WordTrace tailWord_7658975 prefixEnd_7658975 1310911831923092319596507 := by
  unfold tailWord_7658975
  simp only [CollatzResearch.WordTrace]
  refine ⟨279345767427849098636026379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186230511618566065757350919 279345767427849098636026379)
  ·
    refine ⟨419018651141773647954039569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279345767427849098636026379 419018651141773647954039569)
    ·
      refine ⟨314263988356330235965529677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419018651141773647954039569 314263988356330235965529677)
      ·
        refine ⟨117848995633623838487073629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314263988356330235965529677 117848995633623838487073629)
        ·
          refine ⟨44193373362608939432652611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117848995633623838487073629 44193373362608939432652611)
          ·
            refine ⟨66290060043913409148978917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44193373362608939432652611 66290060043913409148978917)
            ·
              refine ⟨12429386258233764215433547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66290060043913409148978917 12429386258233764215433547)
              ·
                refine ⟨18644079387350646323150321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12429386258233764215433547 18644079387350646323150321)
                ·
                  refine ⟨13983059540512984742362741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18644079387350646323150321 13983059540512984742362741)
                  ·
                    refine ⟨1310911831923092319596507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13983059540512984742362741 1310911831923092319596507)
                    ·
                      rfl

theorem cell23_7658975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 5].length) (baseStart_7658975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7658975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7658975 prefixEnd_7658975 := by exact prefixLift 7658975
  have htrace : WordTrace (prefixWord ++ tailWord_7658975) baseStart_7658975 baseEnd_7658975 := by
    simpa [prefixWord, tailWord_7658975, baseEnd_7658975] using wordTrace_append hprefix tailTrace_7658975
  have hstable : (prefixWord ++ tailWord_7658975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7658975).length < 2 ^ (prefixWord ++ tailWord_7658975).sum := by decide
  have hdescent : baseEnd_7658975 < baseStart_7658975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7658975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659032 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 1, 4, 3]
def baseStart_7659032 : Nat := 118140960795 + 7659032 * 2 ^ 59
def prefixEnd_7659032 : Nat := 4983230072969 + 3 ^ 40 * 7659032 * 2
def baseEnd_7659032 : Nat := 3932764764166583235776759

theorem tailTrace_7659032 : CollatzResearch.WordTrace tailWord_7659032 prefixEnd_7659032 3932764764166583235776759 := by
  unfold tailWord_7659032
  simp only [CollatzResearch.WordTrace]
  refine ⟨139673923194321298685425675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186231897592428398247234233 139673923194321298685425675)
  ·
    refine ⟨209510884791481948028138513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139673923194321298685425675 209510884791481948028138513)
    ·
      refine ⟨157133163593611461021103885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209510884791481948028138513 157133163593611461021103885)
      ·
        refine ⟨58924936347604297882913957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157133163593611461021103885 58924936347604297882913957)
        ·
          refine ⟨11048425565175805853046367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58924936347604297882913957 11048425565175805853046367)
          ·
            refine ⟨16572638347763708779569551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11048425565175805853046367 16572638347763708779569551)
            ·
              refine ⟨24858957521645563169354327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16572638347763708779569551 24858957521645563169354327)
              ·
                refine ⟨37288436282468344754031491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24858957521645563169354327 37288436282468344754031491)
                ·
                  refine ⟨55932654423702517131047237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37288436282468344754031491 55932654423702517131047237)
                  ·
                    refine ⟨10487372704444221962071357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55932654423702517131047237 10487372704444221962071357)
                    ·
                      refine ⟨3932764764166583235776759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10487372704444221962071357 3932764764166583235776759)
                      ·
                        rfl

theorem cell23_7659032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_7659032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659032 prefixEnd_7659032 := by exact prefixLift 7659032
  have htrace : WordTrace (prefixWord ++ tailWord_7659032) baseStart_7659032 baseEnd_7659032 := by
    simpa [prefixWord, tailWord_7659032, baseEnd_7659032] using wordTrace_append hprefix tailTrace_7659032
  have hstable : (prefixWord ++ tailWord_7659032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659032).length < 2 ^ (prefixWord ++ tailWord_7659032).sum := by decide
  have hdescent : baseEnd_7659032 < baseStart_7659032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659069 : List Nat := [1, 4, 1, 3, 3, 1, 3, 1, 6]
def baseStart_7659069 : Nat := 118140960795 + 7659069 * 2 ^ 59
def prefixEnd_7659069 : Nat := 4983230072969 + 3 ^ 40 * 7659069 * 2
def baseEnd_7659069 : Nat := 436975973661199954557121

theorem tailTrace_7659069 : CollatzResearch.WordTrace tailWord_7659069 prefixEnd_7659069 436975973661199954557121 := by
  unfold tailWord_7659069
  simp only [CollatzResearch.WordTrace]
  refine ⟨279349195889508552689948261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186232797259672368459965507 279349195889508552689948261)
  ·
    refine ⟨52377974229282853629365299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279349195889508552689948261 52377974229282853629365299)
    ·
      refine ⟨78566961343924280444047949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52377974229282853629365299 78566961343924280444047949)
      ·
        refine ⟨29462610503971605166517981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78566961343924280444047949 29462610503971605166517981)
        ·
          refine ⟨11048478938989351937444243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29462610503971605166517981 11048478938989351937444243)
          ·
            refine ⟨16572718408484027906166365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11048478938989351937444243 16572718408484027906166365)
            ·
              refine ⟨6214769403181510464812387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16572718408484027906166365 6214769403181510464812387)
              ·
                refine ⟨9322154104772265697218581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6214769403181510464812387 9322154104772265697218581)
                ·
                  refine ⟨436975973661199954557121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9322154104772265697218581 436975973661199954557121)
                  ·
                    rfl

theorem cell23_7659069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_7659069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659069 prefixEnd_7659069 := by exact prefixLift 7659069
  have htrace : WordTrace (prefixWord ++ tailWord_7659069) baseStart_7659069 baseEnd_7659069 := by
    simpa [prefixWord, tailWord_7659069, baseEnd_7659069] using wordTrace_append hprefix tailTrace_7659069
  have hstable : (prefixWord ++ tailWord_7659069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659069).length < 2 ^ (prefixWord ++ tailWord_7659069).sum := by decide
  have hdescent : baseEnd_7659069 < baseStart_7659069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659082 : List Nat := [3, 1, 2, 1, 1, 3, 4, 2, 1, 5]
def baseStart_7659082 : Nat := 118140960795 + 7659082 * 2 ^ 59
def prefixEnd_7659082 : Nat := 4983230072969 + 3 ^ 40 * 7659082 * 2
def baseEnd_7659082 : Nat := 1310930146066436013383843

theorem tailTrace_7659082 : CollatzResearch.WordTrace tailWord_7659082 prefixEnd_7659082 1310930146066436013383843 := by
  unfold tailWord_7659082
  simp only [CollatzResearch.WordTrace]
  refine ⟨69837417509615363977542875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186233113358974303940114333 69837417509615363977542875)
  ·
    refine ⟨104756126264423045966314313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69837417509615363977542875 104756126264423045966314313)
    ·
      refine ⟨78567094698317284474735735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104756126264423045966314313 78567094698317284474735735)
      ·
        refine ⟨117850642047475926712103603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78567094698317284474735735 117850642047475926712103603)
        ·
          refine ⟨176775963071213890068155405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117850642047475926712103603 176775963071213890068155405)
          ·
            refine ⟨66290986151705208775558277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176775963071213890068155405 66290986151705208775558277)
            ·
              refine ⟨12429559903444726645417177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66290986151705208775558277 12429559903444726645417177)
              ·
                refine ⟨9322169927583544984062883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12429559903444726645417177 9322169927583544984062883)
                ·
                  refine ⟨13983254891375317476094325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9322169927583544984062883 13983254891375317476094325)
                  ·
                    refine ⟨1310930146066436013383843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13983254891375317476094325 1310930146066436013383843)
                    ·
                      rfl

theorem cell23_7659082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_7659082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659082 prefixEnd_7659082 := by exact prefixLift 7659082
  have htrace : WordTrace (prefixWord ++ tailWord_7659082) baseStart_7659082 baseEnd_7659082 := by
    simpa [prefixWord, tailWord_7659082, baseEnd_7659082] using wordTrace_append hprefix tailTrace_7659082
  have hstable : (prefixWord ++ tailWord_7659082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659082).length < 2 ^ (prefixWord ++ tailWord_7659082).sum := by decide
  have hdescent : baseEnd_7659082 < baseStart_7659082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659122 : List Nat := [3, 2, 1, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_7659122 : Nat := 118140960795 + 7659122 * 2 ^ 59
def prefixEnd_7659122 : Nat := 4983230072969 + 3 ^ 40 * 7659122 * 2
def baseEnd_7659122 : Nat := 3932810977425487883651345

theorem tailTrace_7659122 : CollatzResearch.WordTrace tailWord_7659122 prefixEnd_7659122 3932810977425487883651345 := by
  unfold tailWord_7659122
  simp only [CollatzResearch.WordTrace]
  refine ⟨69837782239579135685406905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186234085972211028494418413 69837782239579135685406905)
  ·
    refine ⟨52378336679684351764055179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69837782239579135685406905 52378336679684351764055179)
    ·
      refine ⟨78567505019526527646082769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52378336679684351764055179 78567505019526527646082769)
      ·
        refine ⟨58925628764644895734562077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78567505019526527646082769 58925628764644895734562077)
        ·
          refine ⟨22097110786741835900460779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58925628764644895734562077 22097110786741835900460779)
          ·
            refine ⟨33145666180112753850691169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22097110786741835900460779 33145666180112753850691169)
            ·
              refine ⟨24859249635084565388018377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33145666180112753850691169 24859249635084565388018377)
              ·
                refine ⟨18644437226313424041013783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24859249635084565388018377 18644437226313424041013783)
                ·
                  refine ⟨27966655839470136061520675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18644437226313424041013783 27966655839470136061520675)
                  ·
                    refine ⟨41949983759205204092281013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27966655839470136061520675 41949983759205204092281013)
                    ·
                      refine ⟨3932810977425487883651345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41949983759205204092281013 3932810977425487883651345)
                      ·
                        rfl

theorem cell23_7659122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_7659122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659122 prefixEnd_7659122 := by exact prefixLift 7659122
  have htrace : WordTrace (prefixWord ++ tailWord_7659122) baseStart_7659122 baseEnd_7659122 := by
    simpa [prefixWord, tailWord_7659122, baseEnd_7659122] using wordTrace_append hprefix tailTrace_7659122
  have hstable : (prefixWord ++ tailWord_7659122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659122).length < 2 ^ (prefixWord ++ tailWord_7659122).sum := by decide
  have hdescent : baseEnd_7659122 < baseStart_7659122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659152 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 6, 1, 3]
def baseStart_7659152 : Nat := 118140960795 + 7659152 * 2 ^ 59
def prefixEnd_7659152 : Nat := 4983230072969 + 3 ^ 40 * 7659152 * 2
def baseEnd_7659152 : Nat := 3932826381845122766276207

theorem tailTrace_7659152 : CollatzResearch.WordTrace tailWord_7659152 prefixEnd_7659152 3932826381845122766276207 := by
  unfold tailWord_7659152
  simp only [CollatzResearch.WordTrace]
  refine ⟨139676111574103928932609855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186234815432138571910146473 139676111574103928932609855)
  ·
    refine ⟨209514167361155893398914783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139676111574103928932609855 209514167361155893398914783)
    ·
      refine ⟨314271251041733840098372175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209514167361155893398914783 314271251041733840098372175)
      ·
        refine ⟨471406876562600760147558263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314271251041733840098372175 471406876562600760147558263)
        ·
          refine ⟨707110314843901140221337395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471406876562600760147558263 707110314843901140221337395)
          ·
            refine ⟨1060665472265851710332006093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707110314843901140221337395 1060665472265851710332006093)
            ·
              refine ⟨397749552099694391374502285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1060665472265851710332006093 397749552099694391374502285)
              ·
                refine ⟨149156082037385396765438357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 397749552099694391374502285 149156082037385396765438357)
                ·
                  refine ⟨6991691345502440473379923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 149156082037385396765438357 6991691345502440473379923)
                  ·
                    refine ⟨10487537018253660710069885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6991691345502440473379923 10487537018253660710069885)
                    ·
                      refine ⟨3932826381845122766276207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10487537018253660710069885 3932826381845122766276207)
                      ·
                        rfl

theorem cell23_7659152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 6, 1, 3].length) (baseStart_7659152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659152 prefixEnd_7659152 := by exact prefixLift 7659152
  have htrace : WordTrace (prefixWord ++ tailWord_7659152) baseStart_7659152 baseEnd_7659152 := by
    simpa [prefixWord, tailWord_7659152, baseEnd_7659152] using wordTrace_append hprefix tailTrace_7659152
  have hstable : (prefixWord ++ tailWord_7659152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659152).length < 2 ^ (prefixWord ++ tailWord_7659152).sum := by decide
  have hdescent : baseEnd_7659152 < baseStart_7659152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659156 : List Nat := [2, 4, 2, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_7659156 : Nat := 118140960795 + 7659156 * 2 ^ 59
def prefixEnd_7659156 : Nat := 4983230072969 + 3 ^ 40 * 7659156 * 2
def baseEnd_7659156 : Nat := 3932828435767740750626189

theorem tailTrace_7659156 : CollatzResearch.WordTrace tailWord_7659156 prefixEnd_7659156 3932828435767740750626189 := by
  unfold tailWord_7659156
  simp only [CollatzResearch.WordTrace]
  refine ⟨139676184520096683274182661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186234912693462244365576881 139676184520096683274182661)
  ·
    refine ⟨26189284597518128113909249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139676184520096683274182661 26189284597518128113909249)
    ·
      refine ⟨19641963448138596085431937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26189284597518128113909249 19641963448138596085431937)
      ·
        refine ⟨14731472586103947064073953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19641963448138596085431937 14731472586103947064073953)
        ·
          refine ⟨11048604439577960298055465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14731472586103947064073953 11048604439577960298055465)
          ·
            refine ⟨8286453329683470223541599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11048604439577960298055465 8286453329683470223541599)
            ·
              refine ⟨12429679994525205335312399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8286453329683470223541599 12429679994525205335312399)
              ·
                refine ⟨18644519991787808002968599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12429679994525205335312399 18644519991787808002968599)
                ·
                  refine ⟨27966779987681712004452899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18644519991787808002968599 27966779987681712004452899)
                  ·
                    refine ⟨41950169981522568006679349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27966779987681712004452899 41950169981522568006679349)
                    ·
                      refine ⟨3932828435767740750626189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41950169981522568006679349 3932828435767740750626189)
                      ·
                        rfl

theorem cell23_7659156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_7659156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659156 prefixEnd_7659156 := by exact prefixLift 7659156
  have htrace : WordTrace (prefixWord ++ tailWord_7659156) baseStart_7659156 baseEnd_7659156 := by
    simpa [prefixWord, tailWord_7659156, baseEnd_7659156] using wordTrace_append hprefix tailTrace_7659156
  have hstable : (prefixWord ++ tailWord_7659156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659156).length < 2 ^ (prefixWord ++ tailWord_7659156).sum := by decide
  have hdescent : baseEnd_7659156 < baseStart_7659156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659195 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 5]
def baseStart_7659195 : Nat := 118140960795 + 7659195 * 2 ^ 59
def prefixEnd_7659195 : Nat := 4983230072969 + 3 ^ 40 * 7659195 * 2
def baseEnd_7659195 : Nat := 3932848461513266098038509

theorem tailTrace_7659195 : CollatzResearch.WordTrace tailWord_7659195 prefixEnd_7659195 3932848461513266098038509 := by
  unfold tailWord_7659195
  simp only [CollatzResearch.WordTrace]
  refine ⟨279353791487052076209035039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186235860991368050806023359 279353791487052076209035039)
  ·
    refine ⟨419030687230578114313552559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279353791487052076209035039 419030687230578114313552559)
    ·
      refine ⟨628546030845867171470328839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419030687230578114313552559 628546030845867171470328839)
      ·
        refine ⟨942819046268800757205493259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628546030845867171470328839 942819046268800757205493259)
        ·
          refine ⟨1414228569403201135808239889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942819046268800757205493259 1414228569403201135808239889)
          ·
            refine ⟨1060671427052400851856179917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1414228569403201135808239889 1060671427052400851856179917)
            ·
              refine ⟨397751785144650319446067469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1060671427052400851856179917 397751785144650319446067469)
              ·
                refine ⟨149156919429243869792275301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 397751785144650319446067469 149156919429243869792275301)
                ·
                  refine ⟨27966922392983225586051619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149156919429243869792275301 27966922392983225586051619)
                  ·
                    refine ⟨41950383589474838379077429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27966922392983225586051619 41950383589474838379077429)
                    ·
                      refine ⟨3932848461513266098038509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41950383589474838379077429 3932848461513266098038509)
                      ·
                        rfl

theorem cell23_7659195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 5].length) (baseStart_7659195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659195 prefixEnd_7659195 := by exact prefixLift 7659195
  have htrace : WordTrace (prefixWord ++ tailWord_7659195) baseStart_7659195 baseEnd_7659195 := by
    simpa [prefixWord, tailWord_7659195, baseEnd_7659195] using wordTrace_append hprefix tailTrace_7659195
  have hstable : (prefixWord ++ tailWord_7659195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659195).length < 2 ^ (prefixWord ++ tailWord_7659195).sum := by decide
  have hdescent : baseEnd_7659195 < baseStart_7659195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659226 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2]
def baseStart_7659226 : Nat := 118140960795 + 7659226 * 2 ^ 59
def prefixEnd_7659226 : Nat := 4983230072969 + 3 ^ 40 * 7659226 * 2
def baseEnd_7659226 : Nat := 3932864379413555476750867

theorem tailTrace_7659226 : CollatzResearch.WordTrace tailWord_7659226 prefixEnd_7659226 3932864379413555476750867 := by
  unfold tailWord_7659226
  simp only [CollatzResearch.WordTrace]
  refine ⟨69838730537484942125853383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186236614766626512335609021 69838730537484942125853383)
  ·
    refine ⟨104758095806227413188780075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69838730537484942125853383 104758095806227413188780075)
    ·
      refine ⟨157137143709341119783170113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104758095806227413188780075 157137143709341119783170113)
      ·
        refine ⟨117852857782005839837377585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157137143709341119783170113 117852857782005839837377585)
        ·
          refine ⟨88389643336504379878033189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117852857782005839837377585 88389643336504379878033189)
          ·
            refine ⟨16573058125594571227131223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88389643336504379878033189 16573058125594571227131223)
            ·
              refine ⟨24859587188391856840696835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16573058125594571227131223 24859587188391856840696835)
              ·
                refine ⟨37289380782587785261045253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24859587188391856840696835 37289380782587785261045253)
                ·
                  refine ⟨6991758896735209736445985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37289380782587785261045253 6991758896735209736445985)
                  ·
                    refine ⟨5243819172551407302334489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6991758896735209736445985 5243819172551407302334489)
                    ·
                      refine ⟨3932864379413555476750867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5243819172551407302334489 3932864379413555476750867)
                      ·
                        rfl

theorem cell23_7659226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_7659226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659226 prefixEnd_7659226 := by exact prefixLift 7659226
  have htrace : WordTrace (prefixWord ++ tailWord_7659226) baseStart_7659226 baseEnd_7659226 := by
    simpa [prefixWord, tailWord_7659226, baseEnd_7659226] using wordTrace_append hprefix tailTrace_7659226
  have hstable : (prefixWord ++ tailWord_7659226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659226).length < 2 ^ (prefixWord ++ tailWord_7659226).sum := by decide
  have hdescent : baseEnd_7659226 < baseStart_7659226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659272 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_7659272 : Nat := 118140960795 + 7659272 * 2 ^ 59
def prefixEnd_7659272 : Nat := 4983230072969 + 3 ^ 40 * 7659272 * 2
def baseEnd_7659272 : Nat := 3932887999523662296775655

theorem tailTrace_7659272 : CollatzResearch.WordTrace tailWord_7659272 prefixEnd_7659272 3932887999523662296775655 := by
  unfold tailWord_7659272
  simp only [CollatzResearch.WordTrace]
  refine ⟨139678299953886559179794035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186237733271848745573058713 139678299953886559179794035)
  ·
    refine ⟨209517449930829838769691053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139678299953886559179794035 209517449930829838769691053)
    ·
      refine ⟨78569043724061189538634145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209517449930829838769691053 78569043724061189538634145)
      ·
        refine ⟨58926782793045892153975609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78569043724061189538634145 58926782793045892153975609)
        ·
          refine ⟨44195087094784419115481707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58926782793045892153975609 44195087094784419115481707)
          ·
            refine ⟨66292630642176628673222561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44195087094784419115481707 66292630642176628673222561)
            ·
              refine ⟨49719472981632471504916921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66292630642176628673222561 49719472981632471504916921)
              ·
                refine ⟨37289604736224353628687691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49719472981632471504916921 37289604736224353628687691)
                ·
                  refine ⟨55934407104336530443031537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37289604736224353628687691 55934407104336530443031537)
                  ·
                    refine ⟨41950805328252397832273653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55934407104336530443031537 41950805328252397832273653)
                    ·
                      refine ⟨3932887999523662296775655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41950805328252397832273653 3932887999523662296775655)
                      ·
                        rfl

theorem cell23_7659272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_7659272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659272 prefixEnd_7659272 := by exact prefixLift 7659272
  have htrace : WordTrace (prefixWord ++ tailWord_7659272) baseStart_7659272 baseEnd_7659272 := by
    simpa [prefixWord, tailWord_7659272, baseEnd_7659272] using wordTrace_append hprefix tailTrace_7659272
  have hstable : (prefixWord ++ tailWord_7659272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659272).length < 2 ^ (prefixWord ++ tailWord_7659272).sum := by decide
  have hdescent : baseEnd_7659272 < baseStart_7659272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659299 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 2, 4, 2]
def baseStart_7659299 : Nat := 118140960795 + 7659299 * 2 ^ 59
def prefixEnd_7659299 : Nat := 4983230072969 + 3 ^ 40 * 7659299 * 2
def baseEnd_7659299 : Nat := 3932901863501333691138031

theorem tailTrace_7659299 : CollatzResearch.WordTrace tailWord_7659299 prefixEnd_7659299 3932901863501333691138031 := by
  unfold tailWord_7659299
  simp only [CollatzResearch.WordTrace]
  refine ⟨279357584678675301970820951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186238389785783534647213967 279357584678675301970820951)
  ·
    refine ⟨419036377018012952956231427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279357584678675301970820951 419036377018012952956231427)
    ·
      refine ⟨628554565527019429434347141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419036377018012952956231427 628554565527019429434347141)
      ·
        refine ⟨117853981036316143018940089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 628554565527019429434347141 117853981036316143018940089)
        ·
          refine ⟨88390485777237107264205067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117853981036316143018940089 88390485777237107264205067)
          ·
            refine ⟨132585728665855660896307601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88390485777237107264205067 132585728665855660896307601)
            ·
              refine ⟨99439296499391745672230701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132585728665855660896307601 99439296499391745672230701)
              ·
                refine ⟨37289736187271904627086513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99439296499391745672230701 37289736187271904627086513)
                ·
                  refine ⟨27967302140453928470314885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37289736187271904627086513 27967302140453928470314885)
                  ·
                    refine ⟨5243869151335111588184041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27967302140453928470314885 5243869151335111588184041)
                    ·
                      refine ⟨3932901863501333691138031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5243869151335111588184041 3932901863501333691138031)
                      ·
                        rfl

theorem cell23_7659299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_7659299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659299 prefixEnd_7659299 := by exact prefixLift 7659299
  have htrace : WordTrace (prefixWord ++ tailWord_7659299) baseStart_7659299 baseEnd_7659299 := by
    simpa [prefixWord, tailWord_7659299, baseEnd_7659299] using wordTrace_append hprefix tailTrace_7659299
  have hstable : (prefixWord ++ tailWord_7659299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659299).length < 2 ^ (prefixWord ++ tailWord_7659299).sum := by decide
  have hdescent : baseEnd_7659299 < baseStart_7659299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659316 : List Nat := [2, 5, 1, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_7659316 : Nat := 118140960795 + 7659316 * 2 ^ 59
def prefixEnd_7659316 : Nat := 4983230072969 + 3 ^ 40 * 7659316 * 2
def baseEnd_7659316 : Nat := 3932910592672460124625453

theorem tailTrace_7659316 : CollatzResearch.WordTrace tailWord_7659316 prefixEnd_7659316 3932910592672460124625453 := by
  unfold tailWord_7659316
  simp only [CollatzResearch.WordTrace]
  refine ⟨139679102359806856937094901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186238803146409142582793201 139679102359806856937094901)
  ·
    refine ⟨13094915846231892837852647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139679102359806856937094901 13094915846231892837852647)
    ·
      refine ⟨19642373769347839256778971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13094915846231892837852647 19642373769347839256778971)
      ·
        refine ⟨29463560654021758885168457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19642373769347839256778971 29463560654021758885168457)
        ·
          refine ⟨22097670490516319163876343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29463560654021758885168457 22097670490516319163876343)
          ·
            refine ⟨33146505735774478745814515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22097670490516319163876343 33146505735774478745814515)
            ·
              refine ⟨49719758603661718118721773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33146505735774478745814515 49719758603661718118721773)
              ·
                refine ⟨18644909476373144294520665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49719758603661718118721773 18644909476373144294520665)
                ·
                  refine ⟨13983682107279858220890499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18644909476373144294520665 13983682107279858220890499)
                  ·
                    refine ⟨20975523160919787331335749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13983682107279858220890499 20975523160919787331335749)
                    ·
                      refine ⟨3932910592672460124625453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20975523160919787331335749 3932910592672460124625453)
                      ·
                        rfl

theorem cell23_7659316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_7659316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659316 prefixEnd_7659316 := by exact prefixLift 7659316
  have htrace : WordTrace (prefixWord ++ tailWord_7659316) baseStart_7659316 baseEnd_7659316 := by
    simpa [prefixWord, tailWord_7659316, baseEnd_7659316] using wordTrace_append hprefix tailTrace_7659316
  have hstable : (prefixWord ++ tailWord_7659316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659316).length < 2 ^ (prefixWord ++ tailWord_7659316).sum := by decide
  have hdescent : baseEnd_7659316 < baseStart_7659316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659370 : List Nat := [3, 1, 3, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_7659370 : Nat := 118140960795 + 7659370 * 2 ^ 59
def prefixEnd_7659370 : Nat := 4983230072969 + 3 ^ 40 * 7659370 * 2
def baseEnd_7659370 : Nat := 3932938320627802913350205

theorem tailTrace_7659370 : CollatzResearch.WordTrace tailWord_7659370 prefixEnd_7659370 3932938320627802913350205 := by
  unfold tailWord_7659370
  simp only [CollatzResearch.WordTrace]
  refine ⟨69840043565354520274163891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186240116174278720731103709 69840043565354520274163891)
  ·
    refine ⟨104760065348031780411245837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69840043565354520274163891 104760065348031780411245837)
    ·
      refine ⟨39285024505511917654217189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104760065348031780411245837 39285024505511917654217189)
      ·
        refine ⟨7365942094783484560165723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39285024505511917654217189 7365942094783484560165723)
        ·
          refine ⟨11048913142175226840248585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7365942094783484560165723 11048913142175226840248585)
          ·
            refine ⟨8286684856631420130186439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11048913142175226840248585 8286684856631420130186439)
            ·
              refine ⟨12430027284947130195279659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8286684856631420130186439 12430027284947130195279659)
              ·
                refine ⟨18645040927420695292919489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12430027284947130195279659 18645040927420695292919489)
                ·
                  refine ⟨13983780695565521469689617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18645040927420695292919489 13983780695565521469689617)
                  ·
                    refine ⟨10487835521674141102267213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13983780695565521469689617 10487835521674141102267213)
                    ·
                      refine ⟨3932938320627802913350205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10487835521674141102267213 3932938320627802913350205)
                      ·
                        rfl

theorem cell23_7659370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_7659370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659370 prefixEnd_7659370 := by exact prefixLift 7659370
  have htrace : WordTrace (prefixWord ++ tailWord_7659370) baseStart_7659370 baseEnd_7659370 := by
    simpa [prefixWord, tailWord_7659370, baseEnd_7659370] using wordTrace_append hprefix tailTrace_7659370
  have hstable : (prefixWord ++ tailWord_7659370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659370).length < 2 ^ (prefixWord ++ tailWord_7659370).sum := by decide
  have hdescent : baseEnd_7659370 < baseStart_7659370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659386 : List Nat := [3, 1, 1, 1, 1, 1, 8, 1, 1, 5]
def baseStart_7659386 : Nat := 118140960795 + 7659386 * 2 ^ 59
def prefixEnd_7659386 : Nat := 4983230072969 + 3 ^ 40 * 7659386 * 2
def baseEnd_7659386 : Nat := 1310982178772758283583377

theorem tailTrace_7659386 : CollatzResearch.WordTrace tailWord_7659386 prefixEnd_7659386 1310982178772758283583377 := by
  unfold tailWord_7659386
  simp only [CollatzResearch.WordTrace]
  refine ⟨69840189457340028957309503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186240505219573410552825341 69840189457340028957309503)
  ·
    refine ⟨104760284186010043435964255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69840189457340028957309503 104760284186010043435964255)
    ·
      refine ⟨157140426279015065153946383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104760284186010043435964255 157140426279015065153946383)
      ·
        refine ⟨235710639418522597730919575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157140426279015065153946383 235710639418522597730919575)
        ·
          refine ⟨353565959127783896596379363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235710639418522597730919575 353565959127783896596379363)
          ·
            refine ⟨530348938691675844894569045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353565959127783896596379363 530348938691675844894569045)
            ·
              refine ⟨6215026625293076307358231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 530348938691675844894569045 6215026625293076307358231)
              ·
                refine ⟨9322539937939614461037347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6215026625293076307358231 9322539937939614461037347)
                ·
                  refine ⟨13983809906909421691556021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9322539937939614461037347 13983809906909421691556021)
                  ·
                    refine ⟨1310982178772758283583377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13983809906909421691556021 1310982178772758283583377)
                    ·
                      rfl

theorem cell23_7659386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 1, 5].length) (baseStart_7659386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659386 prefixEnd_7659386 := by exact prefixLift 7659386
  have htrace : WordTrace (prefixWord ++ tailWord_7659386) baseStart_7659386 baseEnd_7659386 := by
    simpa [prefixWord, tailWord_7659386, baseEnd_7659386] using wordTrace_append hprefix tailTrace_7659386
  have hstable : (prefixWord ++ tailWord_7659386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659386).length < 2 ^ (prefixWord ++ tailWord_7659386).sum := by decide
  have hdescent : baseEnd_7659386 < baseStart_7659386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659409 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 3]
def baseStart_7659409 : Nat := 118140960795 + 7659409 * 2 ^ 59
def prefixEnd_7659409 : Nat := 4983230072969 + 3 ^ 40 * 7659409 * 2
def baseEnd_7659409 : Nat := 3932958346373328260762525

theorem tailTrace_7659409 : CollatzResearch.WordTrace tailWord_7659409 prefixEnd_7659409 3932958346373328260762525 := by
  unfold tailWord_7659409
  simp only [CollatzResearch.WordTrace]
  refine ⟨279361596708276790757325281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186241064472184527171550187 279361596708276790757325281)
  ·
    refine ⟨209521197531207593067993961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279361596708276790757325281 209521197531207593067993961)
    ·
      refine ⟨157140898148405694800995471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209521197531207593067993961 157140898148405694800995471)
      ·
        refine ⟨235711347222608542201493207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157140898148405694800995471 235711347222608542201493207)
        ·
          refine ⟨353567020833912813302239811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235711347222608542201493207 353567020833912813302239811)
          ·
            refine ⟨530350531250869219953359717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353567020833912813302239811 530350531250869219953359717)
            ·
              refine ⟨99440724609537978741254947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 530350531250869219953359717 99440724609537978741254947)
              ·
                refine ⟨149161086914306968111882421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99440724609537978741254947 149161086914306968111882421)
                ·
                  refine ⟨13983851898216278260488977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149161086914306968111882421 13983851898216278260488977)
                  ·
                    refine ⟨10487888923662208695366733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13983851898216278260488977 10487888923662208695366733)
                    ·
                      refine ⟨3932958346373328260762525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10487888923662208695366733 3932958346373328260762525)
                      ·
                        rfl

theorem cell23_7659409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_7659409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659409 prefixEnd_7659409 := by exact prefixLift 7659409
  have htrace : WordTrace (prefixWord ++ tailWord_7659409) baseStart_7659409 baseEnd_7659409 := by
    simpa [prefixWord, tailWord_7659409, baseEnd_7659409] using wordTrace_append hprefix tailTrace_7659409
  have hstable : (prefixWord ++ tailWord_7659409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659409).length < 2 ^ (prefixWord ++ tailWord_7659409).sum := by decide
  have hdescent : baseEnd_7659409 < baseStart_7659409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659423 : List Nat := [1, 1, 2, 5, 3, 1, 2, 2, 1, 1, 4]
def baseStart_7659423 : Nat := 118140960795 + 7659423 * 2 ^ 59
def prefixEnd_7659423 : Nat := 4983230072969 + 3 ^ 40 * 7659423 * 2
def baseEnd_7659423 : Nat := 3932965535102491205987461

theorem tailTrace_7659423 : CollatzResearch.WordTrace tailWord_7659423 prefixEnd_7659423 3932965535102491205987461 := by
  unfold tailWord_7659423
  simp only [CollatzResearch.WordTrace]
  refine ⟨279362107330226071148334923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186241404886817380765556615 279362107330226071148334923)
  ·
    refine ⟨419043160995339106722502385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279362107330226071148334923 419043160995339106722502385)
    ·
      refine ⟨314282370746504330041876789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419043160995339106722502385 314282370746504330041876789)
      ·
        refine ⟨29463972257484780941425949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 314282370746504330041876789 29463972257484780941425949)
        ·
          refine ⟨11048989596556792853034731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29463972257484780941425949 11048989596556792853034731)
          ·
            refine ⟨16573484394835189279552097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11048989596556792853034731 16573484394835189279552097)
            ·
              refine ⟨12430113296126391959664073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16573484394835189279552097 12430113296126391959664073)
              ·
                refine ⟨9322584972094793969748055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12430113296126391959664073 9322584972094793969748055)
                ·
                  refine ⟨13983877458142190954622083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9322584972094793969748055 13983877458142190954622083)
                  ·
                    refine ⟨20975816187213286431933125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13983877458142190954622083 20975816187213286431933125)
                    ·
                      refine ⟨3932965535102491205987461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20975816187213286431933125 3932965535102491205987461)
                      ·
                        rfl

theorem cell23_7659423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_7659423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659423 prefixEnd_7659423 := by exact prefixLift 7659423
  have htrace : WordTrace (prefixWord ++ tailWord_7659423) baseStart_7659423 baseEnd_7659423 := by
    simpa [prefixWord, tailWord_7659423, baseEnd_7659423] using wordTrace_append hprefix tailTrace_7659423
  have hstable : (prefixWord ++ tailWord_7659423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659423).length < 2 ^ (prefixWord ++ tailWord_7659423).sum := by decide
  have hdescent : baseEnd_7659423 < baseStart_7659423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659439 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 3]
def baseStart_7659439 : Nat := 118140960795 + 7659439 * 2 ^ 59
def prefixEnd_7659439 : Nat := 4983230072969 + 3 ^ 40 * 7659439 * 2
def baseEnd_7659439 : Nat := 3932973750792963143387387

theorem tailTrace_7659439 : CollatzResearch.WordTrace tailWord_7659439 prefixEnd_7659439 3932973750792963143387387 := by
  unfold tailWord_7659439
  simp only [CollatzResearch.WordTrace]
  refine ⟨279362690898168105880917371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186241793932112070587278247 279362690898168105880917371)
  ·
    refine ⟨419044036347252158821376057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279362690898168105880917371 419044036347252158821376057)
    ·
      refine ⟨314283027260439119116032043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419044036347252158821376057 314283027260439119116032043)
      ·
        refine ⟨471424540890658678674048065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314283027260439119116032043 471424540890658678674048065)
        ·
          refine ⟨353568405667994009005536049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471424540890658678674048065 353568405667994009005536049)
          ·
            refine ⟨265176304250995506754152037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353568405667994009005536049 265176304250995506754152037)
            ·
              refine ⟨49720557047061657516403507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265176304250995506754152037 49720557047061657516403507)
              ·
                refine ⟨74580835570592486274605261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49720557047061657516403507 74580835570592486274605261)
                ·
                  refine ⟨27967813338972182352976973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74580835570592486274605261 27967813338972182352976973)
                  ·
                    refine ⟨10487930002114568382366365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27967813338972182352976973 10487930002114568382366365)
                    ·
                      refine ⟨3932973750792963143387387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10487930002114568382366365 3932973750792963143387387)
                      ·
                        rfl

theorem cell23_7659439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 3].length) (baseStart_7659439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659439 prefixEnd_7659439 := by exact prefixLift 7659439
  have htrace : WordTrace (prefixWord ++ tailWord_7659439) baseStart_7659439 baseEnd_7659439 := by
    simpa [prefixWord, tailWord_7659439, baseEnd_7659439] using wordTrace_append hprefix tailTrace_7659439
  have hstable : (prefixWord ++ tailWord_7659439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659439).length < 2 ^ (prefixWord ++ tailWord_7659439).sum := by decide
  have hdescent : baseEnd_7659439 < baseStart_7659439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659456 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 4, 1, 3]
def baseStart_7659456 : Nat := 118140960795 + 7659456 * 2 ^ 59
def prefixEnd_7659456 : Nat := 4983230072969 + 3 ^ 40 * 7659456 * 2
def baseEnd_7659456 : Nat := 3932982479964089576874809

theorem tailTrace_7659456 : CollatzResearch.WordTrace tailWord_7659456 prefixEnd_7659456 3932982479964089576874809 := by
  unfold tailWord_7659456
  simp only [CollatzResearch.WordTrace]
  refine ⟨139681655469553258892143111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186242207292737678522857481 139681655469553258892143111)
  ·
    refine ⟨209522483204329888338214667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139681655469553258892143111 209522483204329888338214667)
    ·
      refine ⟨314283724806494832507322001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209522483204329888338214667 314283724806494832507322001)
      ·
        refine ⟨235712793604871124380491501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314283724806494832507322001 235712793604871124380491501)
        ·
          refine ⟨88392297601826671642684313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235712793604871124380491501 88392297601826671642684313)
          ·
            refine ⟨66294223201370003732013235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88392297601826671642684313 66294223201370003732013235)
            ·
              refine ⟨99441334802055005598019853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66294223201370003732013235 99441334802055005598019853)
              ·
                refine ⟨37290500550770627099257445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99441334802055005598019853 37290500550770627099257445)
                ·
                  refine ⟨6991968853269492581110771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37290500550770627099257445 6991968853269492581110771)
                  ·
                    refine ⟨10487953279904238871666157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6991968853269492581110771 10487953279904238871666157)
                    ·
                      refine ⟨3932982479964089576874809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10487953279904238871666157 3932982479964089576874809)
                      ·
                        rfl

theorem cell23_7659456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 4, 1, 3].length) (baseStart_7659456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659456 prefixEnd_7659456 := by exact prefixLift 7659456
  have htrace : WordTrace (prefixWord ++ tailWord_7659456) baseStart_7659456 baseEnd_7659456 := by
    simpa [prefixWord, tailWord_7659456, baseEnd_7659456] using wordTrace_append hprefix tailTrace_7659456
  have hstable : (prefixWord ++ tailWord_7659456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659456).length < 2 ^ (prefixWord ++ tailWord_7659456).sum := by decide
  have hdescent : baseEnd_7659456 < baseStart_7659456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659490 : List Nat := [3, 3, 3, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_7659490 : Nat := 118140960795 + 7659490 * 2 ^ 59
def prefixEnd_7659490 : Nat := 4983230072969 + 3 ^ 40 * 7659490 * 2
def baseEnd_7659490 : Nat := 3932999938306342443849653

theorem tailTrace_7659490 : CollatzResearch.WordTrace tailWord_7659490 prefixEnd_7659490 3932999938306342443849653 := by
  unfold tailWord_7659490
  simp only [CollatzResearch.WordTrace]
  refine ⟨69841137755245835397755981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186243034013988894394015949 69841137755245835397755981)
  ·
    refine ⟨26190426658217188274158493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69841137755245835397755981 26190426658217188274158493)
    ·
      refine ⟨9821409996831445602809435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26190426658217188274158493 9821409996831445602809435)
      ·
        refine ⟨14732114995247168404214153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9821409996831445602809435 14732114995247168404214153)
        ·
          refine ⟨11049086246435376303160615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14732114995247168404214153 11049086246435376303160615)
          ·
            refine ⟨16573629369653064454740923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11049086246435376303160615 16573629369653064454740923)
            ·
              refine ⟨24860444054479596682111385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16573629369653064454740923 24860444054479596682111385)
              ·
                refine ⟨18645333040859697511583539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24860444054479596682111385 18645333040859697511583539)
                ·
                  refine ⟨27967999561289546267375309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18645333040859697511583539 27967999561289546267375309)
                  ·
                    refine ⟨10487999835483579850265741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27967999561289546267375309 10487999835483579850265741)
                    ·
                      refine ⟨3932999938306342443849653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10487999835483579850265741 3932999938306342443849653)
                      ·
                        rfl

theorem cell23_7659490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_7659490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659490 prefixEnd_7659490 := by exact prefixLift 7659490
  have htrace : WordTrace (prefixWord ++ tailWord_7659490) baseStart_7659490 baseEnd_7659490 := by
    simpa [prefixWord, tailWord_7659490, baseEnd_7659490] using wordTrace_append hprefix tailTrace_7659490
  have hstable : (prefixWord ++ tailWord_7659490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659490).length < 2 ^ (prefixWord ++ tailWord_7659490).sum := by decide
  have hdescent : baseEnd_7659490 < baseStart_7659490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659499 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 3]
def baseStart_7659499 : Nat := 118140960795 + 7659499 * 2 ^ 59
def prefixEnd_7659499 : Nat := 4983230072969 + 3 ^ 40 * 7659499 * 2
def baseEnd_7659499 : Nat := 3933004559632232908637111

theorem tailTrace_7659499 : CollatzResearch.WordTrace tailWord_7659499 prefixEnd_7659499 3933004559632232908637111 := by
  unfold tailWord_7659499
  simp only [CollatzResearch.WordTrace]
  refine ⟨279364879277950736128101551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186243252851967157418734367 279364879277950736128101551)
  ·
    refine ⟨419047318916926104192152327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279364879277950736128101551 419047318916926104192152327)
    ·
      refine ⟨628570978375389156288228491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419047318916926104192152327 628570978375389156288228491)
      ·
        refine ⟨942856467563083734432342737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628570978375389156288228491 942856467563083734432342737)
        ·
          refine ⟨707142350672312800824257053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 942856467563083734432342737 707142350672312800824257053)
          ·
            refine ⟨265178381502117300309096395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 707142350672312800824257053 265178381502117300309096395)
            ·
              refine ⟨397767572253175950463644593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265178381502117300309096395 397767572253175950463644593)
              ·
                refine ⟨298325679189881962847733445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397767572253175950463644593 298325679189881962847733445)
                ·
                  refine ⟨55936064848102868033950021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298325679189881962847733445 55936064848102868033950021)
                  ·
                    refine ⟨10488012159019287756365629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55936064848102868033950021 10488012159019287756365629)
                    ·
                      refine ⟨3933004559632232908637111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10488012159019287756365629 3933004559632232908637111)
                      ·
                        rfl

theorem cell23_7659499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 3].length) (baseStart_7659499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659499 prefixEnd_7659499 := by exact prefixLift 7659499
  have htrace : WordTrace (prefixWord ++ tailWord_7659499) baseStart_7659499 baseEnd_7659499 := by
    simpa [prefixWord, tailWord_7659499, baseEnd_7659499] using wordTrace_append hprefix tailTrace_7659499
  have hstable : (prefixWord ++ tailWord_7659499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659499).length < 2 ^ (prefixWord ++ tailWord_7659499).sum := by decide
  have hdescent : baseEnd_7659499 < baseStart_7659499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659530 : List Nat := [3, 1, 2, 2, 4, 1, 2, 1, 1, 4, 2]
def baseStart_7659530 : Nat := 118140960795 + 7659530 * 2 ^ 59
def prefixEnd_7659530 : Nat := 4983230072969 + 3 ^ 40 * 7659530 * 2
def baseEnd_7659530 : Nat := 3933020477532522287349469

theorem tailTrace_7659530 : CollatzResearch.WordTrace tailWord_7659530 prefixEnd_7659530 3933020477532522287349469 := by
  unfold tailWord_7659530
  simp only [CollatzResearch.WordTrace]
  refine ⟨69841502485209607105620011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186244006627225618948320029 69841502485209607105620011)
  ·
    refine ⟨104762253727814410658430017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69841502485209607105620011 104762253727814410658430017)
    ·
      refine ⟨78571690295860807993822513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104762253727814410658430017 78571690295860807993822513)
      ·
        refine ⟨58928767721895605995366885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78571690295860807993822513 58928767721895605995366885)
        ·
          refine ⟨11049143947855426124131291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58928767721895605995366885 11049143947855426124131291)
          ·
            refine ⟨16573715921783139186196937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11049143947855426124131291 16573715921783139186196937)
            ·
              refine ⟨12430286941337354389647703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16573715921783139186196937 12430286941337354389647703)
              ·
                refine ⟨18645430412006031584471555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12430286941337354389647703 18645430412006031584471555)
                ·
                  refine ⟨27968145618009047376707333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18645430412006031584471555 27968145618009047376707333)
                  ·
                    refine ⟨5244027303376696383132625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27968145618009047376707333 5244027303376696383132625)
                    ·
                      refine ⟨3933020477532522287349469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5244027303376696383132625 3933020477532522287349469)
                      ·
                        rfl

theorem cell23_7659530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_7659530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659530 prefixEnd_7659530 := by exact prefixLift 7659530
  have htrace : WordTrace (prefixWord ++ tailWord_7659530) baseStart_7659530 baseEnd_7659530 := by
    simpa [prefixWord, tailWord_7659530, baseEnd_7659530] using wordTrace_append hprefix tailTrace_7659530
  have hstable : (prefixWord ++ tailWord_7659530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659530).length < 2 ^ (prefixWord ++ tailWord_7659530).sum := by decide
  have hdescent : baseEnd_7659530 < baseStart_7659530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659599 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 6]
def baseStart_7659599 : Nat := 118140960795 + 7659599 * 2 ^ 59
def prefixEnd_7659599 : Nat := 4983230072969 + 3 ^ 40 * 7659599 * 2
def baseEnd_7659599 : Nat := 3933055907697682517386651

theorem tailTrace_7659599 : CollatzResearch.WordTrace tailWord_7659599 prefixEnd_7659599 3933055907697682517386651 := by
  unfold tailWord_7659599
  simp only [CollatzResearch.WordTrace]
  refine ⟨279368526577588453206741851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186245684385058968804494567 279368526577588453206741851)
  ·
    refine ⟨419052789866382679810112777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279368526577588453206741851 419052789866382679810112777)
    ·
      refine ⟨314289592399787009857584583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419052789866382679810112777 314289592399787009857584583)
      ·
        refine ⟨471434388599680514786376875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314289592399787009857584583 471434388599680514786376875)
        ·
          refine ⟨707151582899520772179565313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471434388599680514786376875 707151582899520772179565313)
          ·
            refine ⟨530363687174640579134673985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707151582899520772179565313 530363687174640579134673985)
            ·
              refine ⟨397772765380980434351005489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530363687174640579134673985 397772765380980434351005489)
              ·
                refine ⟨298329574035735325763254117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397772765380980434351005489 298329574035735325763254117)
                ·
                  refine ⟨55936795131700373580610147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298329574035735325763254117 55936795131700373580610147)
                  ·
                    refine ⟨83905192697550560370915221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55936795131700373580610147 83905192697550560370915221)
                    ·
                      refine ⟨3933055907697682517386651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83905192697550560370915221 3933055907697682517386651)
                      ·
                        rfl

theorem cell23_7659599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_7659599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659599 prefixEnd_7659599 := by exact prefixLift 7659599
  have htrace : WordTrace (prefixWord ++ tailWord_7659599) baseStart_7659599 baseEnd_7659599 := by
    simpa [prefixWord, tailWord_7659599, baseEnd_7659599] using wordTrace_append hprefix tailTrace_7659599
  have hstable : (prefixWord ++ tailWord_7659599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659599).length < 2 ^ (prefixWord ++ tailWord_7659599).sum := by decide
  have hdescent : baseEnd_7659599 < baseStart_7659599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659609 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 10]
def baseStart_7659609 : Nat := 118140960795 + 7659609 * 2 ^ 59
def prefixEnd_7659609 : Nat := 4983230072969 + 3 ^ 40 * 7659609 * 2
def baseEnd_7659609 : Nat := 437006782500469719806845

theorem tailTrace_7659609 : CollatzResearch.WordTrace tailWord_7659609 prefixEnd_7659609 437006782500469719806845 := by
  unfold tailWord_7659609
  simp only [CollatzResearch.WordTrace]
  refine ⟨279368891307552224914605881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186245927538368149943070587 279368891307552224914605881)
  ·
    refine ⟨209526668480664168685954411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279368891307552224914605881 209526668480664168685954411)
    ·
      refine ⟨314290002720996253028931617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209526668480664168685954411 314290002720996253028931617)
      ·
        refine ⟨235717502040747189771698713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314290002720996253028931617 235717502040747189771698713)
        ·
          refine ⟨176788126530560392328774035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235717502040747189771698713 176788126530560392328774035)
          ·
            refine ⟨265182189795840588493161053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176788126530560392328774035 265182189795840588493161053)
            ·
              refine ⟨99443321173440220684935395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265182189795840588493161053 99443321173440220684935395)
              ·
                refine ⟨149164981760160331027403093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99443321173440220684935395 149164981760160331027403093)
                ·
                  refine ⟨437006782500469719806845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 149164981760160331027403093 437006782500469719806845)
                  ·
                    rfl

theorem cell23_7659609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 10].length) (baseStart_7659609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659609 prefixEnd_7659609 := by exact prefixLift 7659609
  have htrace : WordTrace (prefixWord ++ tailWord_7659609) baseStart_7659609 baseEnd_7659609 := by
    simpa [prefixWord, tailWord_7659609, baseEnd_7659609] using wordTrace_append hprefix tailTrace_7659609
  have hstable : (prefixWord ++ tailWord_7659609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659609).length < 2 ^ (prefixWord ++ tailWord_7659609).sum := by decide
  have hdescent : baseEnd_7659609 < baseStart_7659609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659623 : List Nat := [1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_7659623 : Nat := 118140960795 + 7659623 * 2 ^ 59
def prefixEnd_7659623 : Nat := 4983230072969 + 3 ^ 40 * 7659623 * 2
def baseEnd_7659623 : Nat := 3933068231233390423486541

theorem tailTrace_7659623 : CollatzResearch.WordTrace tailWord_7659623 prefixEnd_7659623 3933068231233390423486541 := by
  unfold tailWord_7659623
  simp only [CollatzResearch.WordTrace]
  refine ⟨279369401929501505305615523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186246267953001003537077015 279369401929501505305615523)
  ·
    refine ⟨419054102894252257958423285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279369401929501505305615523 419054102894252257958423285)
    ·
      refine ⟨39286322146336149183602183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 419054102894252257958423285 39286322146336149183602183)
      ·
        refine ⟨58929483219504223775403275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39286322146336149183602183 58929483219504223775403275)
        ·
          refine ⟨88394224829256335663104913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58929483219504223775403275 88394224829256335663104913)
          ·
            refine ⟨66295668621942251747328685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88394224829256335663104913 66295668621942251747328685)
            ·
              refine ⟨24860875733228344405248257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66295668621942251747328685 24860875733228344405248257)
              ·
                refine ⟨18645656799921258303936193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24860875733228344405248257 18645656799921258303936193)
                ·
                  refine ⟨13984242599940943727952145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18645656799921258303936193 13984242599940943727952145)
                  ·
                    refine ⟨10488181949955707795964109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13984242599940943727952145 10488181949955707795964109)
                    ·
                      refine ⟨3933068231233390423486541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10488181949955707795964109 3933068231233390423486541)
                      ·
                        rfl

theorem cell23_7659623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_7659623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659623 prefixEnd_7659623 := by exact prefixLift 7659623
  have htrace : WordTrace (prefixWord ++ tailWord_7659623) baseStart_7659623 baseEnd_7659623 := by
    simpa [prefixWord, tailWord_7659623, baseEnd_7659623] using wordTrace_append hprefix tailTrace_7659623
  have hstable : (prefixWord ++ tailWord_7659623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659623).length < 2 ^ (prefixWord ++ tailWord_7659623).sum := by decide
  have hdescent : baseEnd_7659623 < baseStart_7659623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659680 : List Nat := [2, 1, 1, 4, 2, 2, 2, 2, 2, 3, 2]
def baseStart_7659680 : Nat := 118140960795 + 7659680 * 2 ^ 59
def prefixEnd_7659680 : Nat := 4983230072969 + 3 ^ 40 * 7659680 * 2
def baseEnd_7659680 : Nat := 3933097499630696700473779

theorem tailTrace_7659680 : CollatzResearch.WordTrace tailWord_7659680 prefixEnd_7659680 3933097499630696700473779 := by
  unfold tailWord_7659680
  simp only [CollatzResearch.WordTrace]
  refine ⟨139685740445147502020220247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186247653926863336026960329 139685740445147502020220247)
  ·
    refine ⟨209528610667721253030330371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139685740445147502020220247 209528610667721253030330371)
    ·
      refine ⟨314292916001581879545495557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209528610667721253030330371 314292916001581879545495557)
      ·
        refine ⟨58929921750296602414780417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314292916001581879545495557 58929921750296602414780417)
        ·
          refine ⟨44197441312722451811085313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58929921750296602414780417 44197441312722451811085313)
          ·
            refine ⟨33148080984541838858313985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44197441312722451811085313 33148080984541838858313985)
            ·
              refine ⟨24861060738406379143735489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33148080984541838858313985 24861060738406379143735489)
              ·
                refine ⟨18645795553804784357801617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24861060738406379143735489 18645795553804784357801617)
                ·
                  refine ⟨13984346665353588268351213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18645795553804784357801617 13984346665353588268351213)
                  ·
                    refine ⟨5244129999507595600631705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13984346665353588268351213 5244129999507595600631705)
                    ·
                      refine ⟨3933097499630696700473779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5244129999507595600631705 3933097499630696700473779)
                      ·
                        rfl

theorem cell23_7659680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_7659680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659680 prefixEnd_7659680 := by exact prefixLift 7659680
  have htrace : WordTrace (prefixWord ++ tailWord_7659680) baseStart_7659680 baseEnd_7659680 := by
    simpa [prefixWord, tailWord_7659680, baseEnd_7659680] using wordTrace_append hprefix tailTrace_7659680
  have hstable : (prefixWord ++ tailWord_7659680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659680).length < 2 ^ (prefixWord ++ tailWord_7659680).sum := by decide
  have hdescent : baseEnd_7659680 < baseStart_7659680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659696 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 3]
def baseStart_7659696 : Nat := 118140960795 + 7659696 * 2 ^ 59
def prefixEnd_7659696 : Nat := 4983230072969 + 3 ^ 40 * 7659696 * 2
def baseEnd_7659696 : Nat := 3933105715321168637873705

theorem tailTrace_7659696 : CollatzResearch.WordTrace tailWord_7659696 prefixEnd_7659696 3933105715321168637873705 := by
  unfold tailWord_7659696
  simp only [CollatzResearch.WordTrace]
  refine ⟨139686032229118519386511471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186248042972158025848681961 139686032229118519386511471)
  ·
    refine ⟨209529048343677779079767207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139686032229118519386511471 209529048343677779079767207)
    ·
      refine ⟨314293572515516668619650811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209529048343677779079767207 314293572515516668619650811)
      ·
        refine ⟨471440358773275002929476217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314293572515516668619650811 471440358773275002929476217)
        ·
          refine ⟨353580269079956252197107163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471440358773275002929476217 353580269079956252197107163)
          ·
            refine ⟨530370403619934378295660745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353580269079956252197107163 530370403619934378295660745)
            ·
              refine ⟨397777802714950783721745559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530370403619934378295660745 397777802714950783721745559)
              ·
                refine ⟨596666704072426175582618339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397777802714950783721745559 596666704072426175582618339)
                ·
                  refine ⟨895000056108639263373927509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596666704072426175582618339 895000056108639263373927509)
                  ·
                    refine ⟨10488281907523116367663213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 895000056108639263373927509 10488281907523116367663213)
                    ·
                      refine ⟨3933105715321168637873705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10488281907523116367663213 3933105715321168637873705)
                      ·
                        rfl

theorem cell23_7659696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 3].length) (baseStart_7659696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659696 prefixEnd_7659696 := by exact prefixLift 7659696
  have htrace : WordTrace (prefixWord ++ tailWord_7659696) baseStart_7659696 baseEnd_7659696 := by
    simpa [prefixWord, tailWord_7659696, baseEnd_7659696] using wordTrace_append hprefix tailTrace_7659696
  have hstable : (prefixWord ++ tailWord_7659696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659696).length < 2 ^ (prefixWord ++ tailWord_7659696).sum := by decide
  have hdescent : baseEnd_7659696 < baseStart_7659696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659703 : List Nat := [1, 1, 3, 1, 4, 3, 2, 1, 1, 6]
def baseStart_7659703 : Nat := 118140960795 + 7659703 * 2 ^ 59
def prefixEnd_7659703 : Nat := 4983230072969 + 3 ^ 40 * 7659703 * 2
def baseEnd_7659703 : Nat := 1311036436561916703495391

theorem tailTrace_7659703 : CollatzResearch.WordTrace tailWord_7659703 prefixEnd_7659703 1311036436561916703495391 := by
  unfold tailWord_7659703
  simp only [CollatzResearch.WordTrace]
  refine ⟨279372319769211678968527763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186248213179474452645685175 279372319769211678968527763)
  ·
    refine ⟨419058479653817518452791645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279372319769211678968527763 419058479653817518452791645)
    ·
      refine ⟨157146929870181569419796867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419058479653817518452791645 157146929870181569419796867)
      ·
        refine ⟨235720394805272354129695301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157146929870181569419796867 235720394805272354129695301)
        ·
          refine ⟨44197574025988566399317869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235720394805272354129695301 44197574025988566399317869)
          ·
            refine ⟨16574090259745712399744201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44197574025988566399317869 16574090259745712399744201)
            ·
              refine ⟨12430567694809284299808151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16574090259745712399744201 12430567694809284299808151)
              ·
                refine ⟨18645851542213926449712227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12430567694809284299808151 18645851542213926449712227)
                ·
                  refine ⟨27968777313320889674568341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18645851542213926449712227 27968777313320889674568341)
                  ·
                    refine ⟨1311036436561916703495391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27968777313320889674568341 1311036436561916703495391)
                    ·
                      rfl

theorem cell23_7659703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_7659703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659703 prefixEnd_7659703 := by exact prefixLift 7659703
  have htrace : WordTrace (prefixWord ++ tailWord_7659703) baseStart_7659703 baseEnd_7659703 := by
    simpa [prefixWord, tailWord_7659703, baseEnd_7659703] using wordTrace_append hprefix tailTrace_7659703
  have hstable : (prefixWord ++ tailWord_7659703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659703).length < 2 ^ (prefixWord ++ tailWord_7659703).sum := by decide
  have hdescent : baseEnd_7659703 < baseStart_7659703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659706 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6]
def baseStart_7659706 : Nat := 118140960795 + 7659706 * 2 ^ 59
def prefixEnd_7659706 : Nat := 4983230072969 + 3 ^ 40 * 7659706 * 2
def baseEnd_7659706 : Nat := 3933110850127713598748659

theorem tailTrace_7659706 : CollatzResearch.WordTrace tailWord_7659706 prefixEnd_7659706 3933110850127713598748659 := by
  unfold tailWord_7659706
  simp only [CollatzResearch.WordTrace]
  refine ⟨69843107297050202620221743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186248286125467206987257981 69843107297050202620221743)
  ·
    refine ⟨104764660945575303930332615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69843107297050202620221743 104764660945575303930332615)
    ·
      refine ⟨157146991418362955895498923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104764660945575303930332615 157146991418362955895498923)
      ·
        refine ⟨235720487127544433843248385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157146991418362955895498923 235720487127544433843248385)
        ·
          refine ⟨176790365345658325382436289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235720487127544433843248385 176790365345658325382436289)
          ·
            refine ⟨132592774009243744036827217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176790365345658325382436289 132592774009243744036827217)
            ·
              refine ⟨99444580506932808027620413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132592774009243744036827217 99444580506932808027620413)
              ·
                refine ⟨37291717690099803010357655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99444580506932808027620413 37291717690099803010357655)
                ·
                  refine ⟨55937576535149704515536483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37291717690099803010357655 55937576535149704515536483)
                  ·
                    refine ⟨83906364802724556773304725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55937576535149704515536483 83906364802724556773304725)
                    ·
                      refine ⟨3933110850127713598748659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83906364802724556773304725 3933110850127713598748659)
                      ·
                        rfl

theorem cell23_7659706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_7659706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659706 prefixEnd_7659706 := by exact prefixLift 7659706
  have htrace : WordTrace (prefixWord ++ tailWord_7659706) baseStart_7659706 baseEnd_7659706 := by
    simpa [prefixWord, tailWord_7659706, baseEnd_7659706] using wordTrace_append hprefix tailTrace_7659706
  have hstable : (prefixWord ++ tailWord_7659706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659706).length < 2 ^ (prefixWord ++ tailWord_7659706).sum := by decide
  have hdescent : baseEnd_7659706 < baseStart_7659706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659714 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_7659714 : Nat := 118140960795 + 7659714 * 2 ^ 59
def prefixEnd_7659714 : Nat := 4983230072969 + 3 ^ 40 * 7659714 * 2
def baseEnd_7659714 : Nat := 3933114957972949567448623

theorem tailTrace_7659714 : CollatzResearch.WordTrace tailWord_7659714 prefixEnd_7659714 3933114957972949567448623 := by
  unfold tailWord_7659714
  simp only [CollatzResearch.WordTrace]
  refine ⟨69843180243042956961794549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186248480648114551898118797 69843180243042956961794549)
  ·
    refine ⟨6547798147785277215168239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69843180243042956961794549 6547798147785277215168239)
    ·
      refine ⟨9821697221677915822752359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6547798147785277215168239 9821697221677915822752359)
      ·
        refine ⟨14732545832516873734128539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9821697221677915822752359 14732545832516873734128539)
        ·
          refine ⟨22098818748775310601192809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14732545832516873734128539 22098818748775310601192809)
          ·
            refine ⟨16574114061581482950894607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22098818748775310601192809 16574114061581482950894607)
            ·
              refine ⟨24861171092372224426341911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16574114061581482950894607 24861171092372224426341911)
              ·
                refine ⟨37291756638558336639512867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24861171092372224426341911 37291756638558336639512867)
                ·
                  refine ⟨55937634957837504959269301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37291756638558336639512867 55937634957837504959269301)
                  ·
                    refine ⟨5244153277297266089931497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55937634957837504959269301 5244153277297266089931497)
                    ·
                      refine ⟨3933114957972949567448623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5244153277297266089931497 3933114957972949567448623)
                      ·
                        rfl

theorem cell23_7659714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_7659714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659714 prefixEnd_7659714 := by exact prefixLift 7659714
  have htrace : WordTrace (prefixWord ++ tailWord_7659714) baseStart_7659714 baseEnd_7659714 := by
    simpa [prefixWord, tailWord_7659714, baseEnd_7659714] using wordTrace_append hprefix tailTrace_7659714
  have hstable : (prefixWord ++ tailWord_7659714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659714).length < 2 ^ (prefixWord ++ tailWord_7659714).sum := by decide
  have hdescent : baseEnd_7659714 < baseStart_7659714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659724 : List Nat := [2, 2, 1, 6, 1, 2, 2, 1, 1, 5]
def baseStart_7659724 : Nat := 118140960795 + 7659724 * 2 ^ 59
def prefixEnd_7659724 : Nat := 4983230072969 + 3 ^ 40 * 7659724 * 2
def baseEnd_7659724 : Nat := 1311040030926498176107859

theorem tailTrace_7659724 : CollatzResearch.WordTrace tailWord_7659724 prefixEnd_7659724 1311040030926498176107859 := by
  unfold tailWord_7659724
  simp only [CollatzResearch.WordTrace]
  refine ⟨139686542851067799777521113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186248723801423733036694817 139686542851067799777521113)
  ·
    refine ⟨104764907138300849833140835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139686542851067799777521113 104764907138300849833140835)
    ·
      refine ⟨157147360707451274749711253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104764907138300849833140835 157147360707451274749711253)
      ·
        refine ⟨7366282533161778503892715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 157147360707451274749711253 7366282533161778503892715)
        ·
          refine ⟨11049423799742667755839073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7366282533161778503892715 11049423799742667755839073)
          ·
            refine ⟨8287067849807000816879305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11049423799742667755839073 8287067849807000816879305)
            ·
              refine ⟨6215300887355250612659479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8287067849807000816879305 6215300887355250612659479)
              ·
                refine ⟨9322951331032875918989219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6215300887355250612659479 9322951331032875918989219)
                ·
                  refine ⟨13984426996549313878483829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9322951331032875918989219 13984426996549313878483829)
                  ·
                    refine ⟨1311040030926498176107859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13984426996549313878483829 1311040030926498176107859)
                    ·
                      rfl

theorem cell23_7659724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 1, 5].length) (baseStart_7659724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659724 prefixEnd_7659724 := by exact prefixLift 7659724
  have htrace : WordTrace (prefixWord ++ tailWord_7659724) baseStart_7659724 baseEnd_7659724 := by
    simpa [prefixWord, tailWord_7659724, baseEnd_7659724] using wordTrace_append hprefix tailTrace_7659724
  have hstable : (prefixWord ++ tailWord_7659724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659724).length < 2 ^ (prefixWord ++ tailWord_7659724).sum := by decide
  have hdescent : baseEnd_7659724 < baseStart_7659724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659733 : List Nat := [1, 3, 2, 4, 2, 1, 10]
def baseStart_7659733 : Nat := 118140960795 + 7659733 * 2 ^ 59
def prefixEnd_7659733 : Nat := 4983230072969 + 3 ^ 40 * 7659733 * 2
def baseEnd_7659733 : Nat := 48557095235868950532235

theorem tailTrace_7659733 : CollatzResearch.WordTrace tailWord_7659733 prefixEnd_7659733 48557095235868950532235 := by
  unfold tailWord_7659733
  simp only [CollatzResearch.WordTrace]
  refine ⟨279373413959102994092119853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186248942639401996061413235 279373413959102994092119853)
  ·
    refine ⟨104765030234663622784544945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279373413959102994092119853 104765030234663622784544945)
    ·
      refine ⟨78573772675997717088408709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104765030234663622784544945 78573772675997717088408709)
      ·
        refine ⟨14732582376749571954076633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78573772675997717088408709 14732582376749571954076633)
        ·
          refine ⟨11049436782562178965557475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14732582376749571954076633 11049436782562178965557475)
          ·
            refine ⟨16574155173843268448336213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11049436782562178965557475 16574155173843268448336213)
            ·
              refine ⟨48557095235868950532235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16574155173843268448336213 48557095235868950532235)
              ·
                rfl

theorem cell23_7659733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 10].length) (baseStart_7659733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659733 prefixEnd_7659733 := by exact prefixLift 7659733
  have htrace : WordTrace (prefixWord ++ tailWord_7659733) baseStart_7659733 baseEnd_7659733 := by
    simpa [prefixWord, tailWord_7659733, baseEnd_7659733] using wordTrace_append hprefix tailTrace_7659733
  have hstable : (prefixWord ++ tailWord_7659733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659733).length < 2 ^ (prefixWord ++ tailWord_7659733).sum := by decide
  have hdescent : baseEnd_7659733 < baseStart_7659733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659757 : List Nat := [1, 5, 1, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_7659757 : Nat := 118140960795 + 7659757 * 2 ^ 59
def prefixEnd_7659757 : Nat := 4983230072969 + 3 ^ 40 * 7659757 * 2
def baseEnd_7659757 : Nat := 3933137037641092899210925

theorem tailTrace_7659757 : CollatzResearch.WordTrace tailWord_7659757 prefixEnd_7659757 3933137037641092899210925 := by
  unfold tailWord_7659757
  simp only [CollatzResearch.WordTrace]
  refine ⟨279374289311016046190993525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186249526207344030793995683 279374289311016046190993525)
  ·
    refine ⟨26191339622907754330405643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279374289311016046190993525 26191339622907754330405643)
    ·
      refine ⟨39287009434361631495608465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26191339622907754330405643 39287009434361631495608465)
      ·
        refine ⟨29465257075771223621706349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39287009434361631495608465 29465257075771223621706349)
        ·
          refine ⟨11049471403414208858139881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29465257075771223621706349 11049471403414208858139881)
          ·
            refine ⟨8287103552560656643604911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11049471403414208858139881 8287103552560656643604911)
            ·
              refine ⟨12430655328840984965407367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8287103552560656643604911 12430655328840984965407367)
              ·
                refine ⟨18645982993261477448111051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12430655328840984965407367 18645982993261477448111051)
                ·
                  refine ⟨27968974489892216172166577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18645982993261477448111051 27968974489892216172166577)
                  ·
                    refine ⟨20976730867419162129124933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27968974489892216172166577 20976730867419162129124933)
                    ·
                      refine ⟨3933137037641092899210925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20976730867419162129124933 3933137037641092899210925)
                      ·
                        rfl

theorem cell23_7659757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_7659757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659757 prefixEnd_7659757 := by exact prefixLift 7659757
  have htrace : WordTrace (prefixWord ++ tailWord_7659757) baseStart_7659757 baseEnd_7659757 := by
    simpa [prefixWord, tailWord_7659757, baseEnd_7659757] using wordTrace_append hprefix tailTrace_7659757
  have hstable : (prefixWord ++ tailWord_7659757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659757).length < 2 ^ (prefixWord ++ tailWord_7659757).sum := by decide
  have hdescent : baseEnd_7659757 < baseStart_7659757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659760 : List Nat := [2, 1, 1, 1, 3, 1, 1, 7, 2, 1, 3]
def baseStart_7659760 : Nat := 118140960795 + 7659760 * 2 ^ 59
def prefixEnd_7659760 : Nat := 4983230072969 + 3 ^ 40 * 7659760 * 2
def baseEnd_7659760 : Nat := 3933138578083056387473411

theorem tailTrace_7659760 : CollatzResearch.WordTrace tailWord_7659760 prefixEnd_7659760 3933138578083056387473411 := by
  unfold tailWord_7659760
  simp only [CollatzResearch.WordTrace]
  refine ⟨139687199365002588851676367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186249599153336785135568489 139687199365002588851676367)
  ·
    refine ⟨209530799047503883277514551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139687199365002588851676367 209530799047503883277514551)
    ·
      refine ⟨314296198571255824916271827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209530799047503883277514551 314296198571255824916271827)
      ·
        refine ⟨471444297856883737374407741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314296198571255824916271827 471444297856883737374407741)
        ·
          refine ⟨176791611696331401515402903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 471444297856883737374407741 176791611696331401515402903)
          ·
            refine ⟨265187417544497102273104355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176791611696331401515402903 265187417544497102273104355)
            ·
              refine ⟨397781126316745653409656533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265187417544497102273104355 397781126316745653409656533)
              ·
                refine ⟨9322995148048726251788825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 397781126316745653409656533 9322995148048726251788825)
                ·
                  refine ⟨6992246361036544688841619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9322995148048726251788825 6992246361036544688841619)
                  ·
                    refine ⟨10488369541554817033262429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6992246361036544688841619 10488369541554817033262429)
                    ·
                      refine ⟨3933138578083056387473411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10488369541554817033262429 3933138578083056387473411)
                      ·
                        rfl

theorem cell23_7659760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 2, 1, 3].length) (baseStart_7659760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659760 prefixEnd_7659760 := by exact prefixLift 7659760
  have htrace : WordTrace (prefixWord ++ tailWord_7659760) baseStart_7659760 baseEnd_7659760 := by
    simpa [prefixWord, tailWord_7659760, baseEnd_7659760] using wordTrace_append hprefix tailTrace_7659760
  have hstable : (prefixWord ++ tailWord_7659760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659760).length < 2 ^ (prefixWord ++ tailWord_7659760).sum := by decide
  have hdescent : baseEnd_7659760 < baseStart_7659760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659776 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 1, 8]
def baseStart_7659776 : Nat := 118140960795 + 7659776 * 2 ^ 59
def prefixEnd_7659776 : Nat := 4983230072969 + 3 ^ 40 * 7659776 * 2
def baseEnd_7659776 : Nat := 1311048931257842774957779

theorem tailTrace_7659776 : CollatzResearch.WordTrace tailWord_7659776 prefixEnd_7659776 1311048931257842774957779 := by
  unfold tailWord_7659776
  simp only [CollatzResearch.WordTrace]
  refine ⟨139687491148973606217967591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186249988198631474957290121 139687491148973606217967591)
  ·
    refine ⟨209531236723460409326951387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139687491148973606217967591 209531236723460409326951387)
    ·
      refine ⟨314296855085190613990427081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209531236723460409326951387 314296855085190613990427081)
      ·
        refine ⟨235722641313892960492820311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314296855085190613990427081 235722641313892960492820311)
        ·
          refine ⟨353583961970839440739230467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235722641313892960492820311 353583961970839440739230467)
          ·
            refine ⟨530375942956259161108845701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353583961970839440739230467 530375942956259161108845701)
            ·
              refine ⟨99445489304298592707908569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 530375942956259161108845701 99445489304298592707908569)
              ·
                refine ⟨74584116978223944530931427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99445489304298592707908569 74584116978223944530931427)
                ·
                  refine ⟨111876175467335916796397141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74584116978223944530931427 111876175467335916796397141)
                  ·
                    refine ⟨1311048931257842774957779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111876175467335916796397141 1311048931257842774957779)
                    ·
                      rfl

theorem cell23_7659776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 8].length) (baseStart_7659776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659776 prefixEnd_7659776 := by exact prefixLift 7659776
  have htrace : WordTrace (prefixWord ++ tailWord_7659776) baseStart_7659776 baseEnd_7659776 := by
    simpa [prefixWord, tailWord_7659776, baseEnd_7659776] using wordTrace_append hprefix tailTrace_7659776
  have hstable : (prefixWord ++ tailWord_7659776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659776).length < 2 ^ (prefixWord ++ tailWord_7659776).sum := by decide
  have hdescent : baseEnd_7659776 < baseStart_7659776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659778 : List Nat := [3, 4, 1, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_7659778 : Nat := 118140960795 + 7659778 * 2 ^ 59
def prefixEnd_7659778 : Nat := 4983230072969 + 3 ^ 40 * 7659778 * 2
def baseEnd_7659778 : Nat := 3933147820734837317048329

theorem tailTrace_7659778 : CollatzResearch.WordTrace tailWord_7659778 prefixEnd_7659778 3933147820734837317048329 := by
  unfold tailWord_7659778
  simp only [CollatzResearch.WordTrace]
  refine ⟨69843763810984991694376997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186250036829293311185005325 69843763810984991694376997)
  ·
    refine ⟨13095705714559685942695687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69843763810984991694376997 13095705714559685942695687)
    ·
      refine ⟨19643558571839528914043531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13095705714559685942695687 19643558571839528914043531)
      ·
        refine ⟨29465337857759293371065297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19643558571839528914043531 29465337857759293371065297)
        ·
          refine ⟨22099003393319470028298973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29465337857759293371065297 22099003393319470028298973)
          ·
            refine ⟨8287126272494801260612115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22099003393319470028298973 8287126272494801260612115)
            ·
              refine ⟨12430689408742201890918173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8287126272494801260612115 12430689408742201890918173)
              ·
                refine ⟨4661508528278325709094315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12430689408742201890918173 4661508528278325709094315)
                ·
                  refine ⟨6992262792417488563641473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4661508528278325709094315 6992262792417488563641473)
                  ·
                    refine ⟨5244197094313116422731105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6992262792417488563641473 5244197094313116422731105)
                    ·
                      refine ⟨3933147820734837317048329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5244197094313116422731105 3933147820734837317048329)
                      ·
                        rfl

theorem cell23_7659778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_7659778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659778 prefixEnd_7659778 := by exact prefixLift 7659778
  have htrace : WordTrace (prefixWord ++ tailWord_7659778) baseStart_7659778 baseEnd_7659778 := by
    simpa [prefixWord, tailWord_7659778, baseEnd_7659778] using wordTrace_append hprefix tailTrace_7659778
  have hstable : (prefixWord ++ tailWord_7659778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659778).length < 2 ^ (prefixWord ++ tailWord_7659778).sum := by decide
  have hdescent : baseEnd_7659778 < baseStart_7659778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659857 : List Nat := [1, 2, 2, 1, 4, 2, 4, 2, 5]
def baseStart_7659857 : Nat := 118140960795 + 7659857 * 2 ^ 59
def prefixEnd_7659857 : Nat := 4983230072969 + 3 ^ 40 * 7659857 * 2
def baseEnd_7659857 : Nat := 437020931745171389773385

theorem tailTrace_7659857 : CollatzResearch.WordTrace tailWord_7659857 prefixEnd_7659857 437020931745171389773385 := by
  unfold tailWord_7659857
  simp only [CollatzResearch.WordTrace]
  refine ⟨279377936610653763269633825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186251957740435842179755883 279377936610653763269633825)
  ·
    refine ⟨209533452457990322452225369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279377936610653763269633825 209533452457990322452225369)
    ·
      refine ⟨157150089343492741839169027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209533452457990322452225369 157150089343492741839169027)
      ·
        refine ⟨235725134015239112758753541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157150089343492741839169027 235725134015239112758753541)
        ·
          refine ⟨44198462627857333642266289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235725134015239112758753541 44198462627857333642266289)
          ·
            refine ⟨33148846970893000231699717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44198462627857333642266289 33148846970893000231699717)
            ·
              refine ⟨6215408807042437543443697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33148846970893000231699717 6215408807042437543443697)
              ·
                refine ⟨4661556605281828157582773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6215408807042437543443697 4661556605281828157582773)
                ·
                  refine ⟨437020931745171389773385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4661556605281828157582773 437020931745171389773385)
                  ·
                    rfl

theorem cell23_7659857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 5].length) (baseStart_7659857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659857 prefixEnd_7659857 := by exact prefixLift 7659857
  have htrace : WordTrace (prefixWord ++ tailWord_7659857) baseStart_7659857 baseEnd_7659857 := by
    simpa [prefixWord, tailWord_7659857, baseEnd_7659857] using wordTrace_append hprefix tailTrace_7659857
  have hstable : (prefixWord ++ tailWord_7659857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659857).length < 2 ^ (prefixWord ++ tailWord_7659857).sum := by decide
  have hdescent : baseEnd_7659857 < baseStart_7659857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659863 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 5]
def baseStart_7659863 : Nat := 118140960795 + 7659863 * 2 ^ 59
def prefixEnd_7659863 : Nat := 4983230072969 + 3 ^ 40 * 7659863 * 2
def baseEnd_7659863 : Nat := 3933191466590469484485437

theorem tailTrace_7659863 : CollatzResearch.WordTrace tailWord_7659863 prefixEnd_7659863 3933191466590469484485437 := by
  unfold tailWord_7659863
  simp only [CollatzResearch.WordTrace]
  refine ⟨279378155448632026294352243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186252103632421350862901495 279378155448632026294352243)
  ·
    refine ⟨419067233172948039441528365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279378155448632026294352243 419067233172948039441528365)
    ·
      refine ⟨157150212439855514790573137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419067233172948039441528365 157150212439855514790573137)
      ·
        refine ⟨117862659329891636092929853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157150212439855514790573137 117862659329891636092929853)
        ·
          refine ⟨44198497248709363534848695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117862659329891636092929853 44198497248709363534848695)
          ·
            refine ⟨66297745873064045302273043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44198497248709363534848695 66297745873064045302273043)
            ·
              refine ⟨99446618809596067953409565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66297745873064045302273043 99446618809596067953409565)
              ·
                refine ⟨37292482053598525482528587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99446618809596067953409565 37292482053598525482528587)
                ·
                  refine ⟨55938723080397788223792881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37292482053598525482528587 55938723080397788223792881)
                  ·
                    refine ⟨41954042310298341167844661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55938723080397788223792881 41954042310298341167844661)
                    ·
                      refine ⟨3933191466590469484485437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41954042310298341167844661 3933191466590469484485437)
                      ·
                        rfl

theorem cell23_7659863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_7659863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659863 prefixEnd_7659863 := by exact prefixLift 7659863
  have htrace : WordTrace (prefixWord ++ tailWord_7659863) baseStart_7659863 baseEnd_7659863 := by
    simpa [prefixWord, tailWord_7659863, baseEnd_7659863] using wordTrace_append hprefix tailTrace_7659863
  have hstable : (prefixWord ++ tailWord_7659863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659863).length < 2 ^ (prefixWord ++ tailWord_7659863).sum := by decide
  have hdescent : baseEnd_7659863 < baseStart_7659863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659890 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_7659890 : Nat := 118140960795 + 7659890 * 2 ^ 59
def prefixEnd_7659890 : Nat := 4983230072969 + 3 ^ 40 * 7659890 * 2
def baseEnd_7659890 : Nat := 3933205330568140878847813

theorem tailTrace_7659890 : CollatzResearch.WordTrace tailWord_7659890 prefixEnd_7659890 3933205330568140878847813 := by
  unfold tailWord_7659890
  simp only [CollatzResearch.WordTrace]
  refine ⟨69844785054883552476396281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186252760146356139937056749 69844785054883552476396281)
  ·
    refine ⟨52383588791162664357297211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69844785054883552476396281 52383588791162664357297211)
    ·
      refine ⟨78575383186743996535945817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52383588791162664357297211 78575383186743996535945817)
      ·
        refine ⟨58931537390057997401959363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78575383186743996535945817 58931537390057997401959363)
        ·
          refine ⟨88397306085086996102939045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58931537390057997401959363 88397306085086996102939045)
          ·
            refine ⟨16574494890953811769301071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88397306085086996102939045 16574494890953811769301071)
            ·
              refine ⟨24861742336430717653951607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16574494890953811769301071 24861742336430717653951607)
              ·
                refine ⟨37292613504646076480927411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24861742336430717653951607 37292613504646076480927411)
                ·
                  refine ⟨55938920256969114721391117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37292613504646076480927411 55938920256969114721391117)
                  ·
                    refine ⟨20977095096363418020521669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55938920256969114721391117 20977095096363418020521669)
                    ·
                      refine ⟨3933205330568140878847813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20977095096363418020521669 3933205330568140878847813)
                      ·
                        rfl

theorem cell23_7659890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_7659890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659890 prefixEnd_7659890 := by exact prefixLift 7659890
  have htrace : WordTrace (prefixWord ++ tailWord_7659890) baseStart_7659890 baseEnd_7659890 := by
    simpa [prefixWord, tailWord_7659890, baseEnd_7659890] using wordTrace_append hprefix tailTrace_7659890
  have hstable : (prefixWord ++ tailWord_7659890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659890).length < 2 ^ (prefixWord ++ tailWord_7659890).sum := by decide
  have hdescent : baseEnd_7659890 < baseStart_7659890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659934 : List Nat := [4, 3, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_7659934 : Nat := 118140960795 + 7659934 * 2 ^ 59
def prefixEnd_7659934 : Nat := 4983230072969 + 3 ^ 40 * 7659934 * 2
def baseEnd_7659934 : Nat := 1311075974572312902232537

theorem tailTrace_7659934 : CollatzResearch.WordTrace tailWord_7659934 prefixEnd_7659934 1311075974572312902232537 := by
  unfold tailWord_7659934
  simp only [CollatzResearch.WordTrace]
  refine ⟨34922593128921850677523357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186253830020916536946791237 34922593128921850677523357)
  ·
    refine ⟨13095972423345694004071259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34922593128921850677523357 13095972423345694004071259)
    ·
      refine ⟨19643958635018541006106889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13095972423345694004071259 19643958635018541006106889)
      ·
        refine ⟨14732968976263905754580167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19643958635018541006106889 14732968976263905754580167)
        ·
          refine ⟨22099453464395858631870251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14732968976263905754580167 22099453464395858631870251)
          ·
            refine ⟨33149180196593787947805377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22099453464395858631870251 33149180196593787947805377)
            ·
              refine ⟨24861885147445340960854033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33149180196593787947805377 24861885147445340960854033)
              ·
                refine ⟨18646413860584005720640525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24861885147445340960854033 18646413860584005720640525)
                ·
                  refine ⟨6992405197719002145240197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18646413860584005720640525 6992405197719002145240197)
                  ·
                    refine ⟨1311075974572312902232537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6992405197719002145240197 1311075974572312902232537)
                    ·
                      rfl

theorem cell23_7659934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_7659934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659934 prefixEnd_7659934 := by exact prefixLift 7659934
  have htrace : WordTrace (prefixWord ++ tailWord_7659934) baseStart_7659934 baseEnd_7659934 := by
    simpa [prefixWord, tailWord_7659934, baseEnd_7659934] using wordTrace_append hprefix tailTrace_7659934
  have hstable : (prefixWord ++ tailWord_7659934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659934).length < 2 ^ (prefixWord ++ tailWord_7659934).sum := by decide
  have hdescent : baseEnd_7659934 < baseStart_7659934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7659997 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_7659997 : Nat := 118140960795 + 7659997 * 2 ^ 59
def prefixEnd_7659997 : Nat := 4983230072969 + 3 ^ 40 * 7659997 * 2
def baseEnd_7659997 : Nat := 3933260272998171960209821

theorem tailTrace_7659997 : CollatzResearch.WordTrace tailWord_7659997 prefixEnd_7659997 3933260272998171960209821 := by
  unfold tailWord_7659997
  simp only [CollatzResearch.WordTrace]
  refine ⟨279383042830146567179730245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186255361886764378119820163 279383042830146567179730245)
  ·
    refine ⟨52384320530652481346199421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279383042830146567179730245 52384320530652481346199421)
    ·
      refine ⟨19644120198994680504824783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52384320530652481346199421 19644120198994680504824783)
      ·
        refine ⟨29466180298492020757237175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19644120198994680504824783 29466180298492020757237175)
        ·
          refine ⟨44199270447738031135855763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29466180298492020757237175 44199270447738031135855763)
          ·
            refine ⟨66298905671607046703783645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44199270447738031135855763 66298905671607046703783645)
            ·
              refine ⟨24862089626852642513918867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66298905671607046703783645 24862089626852642513918867)
              ·
                refine ⟨37293134440278963770878301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24862089626852642513918867 37293134440278963770878301)
                ·
                  refine ⟨13984925415104611414079363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37293134440278963770878301 13984925415104611414079363)
                  ·
                    refine ⟨20977388122656917121119045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13984925415104611414079363 20977388122656917121119045)
                    ·
                      refine ⟨3933260272998171960209821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20977388122656917121119045 3933260272998171960209821)
                      ·
                        rfl

theorem cell23_7659997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_7659997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7659997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7659997 prefixEnd_7659997 := by exact prefixLift 7659997
  have htrace : WordTrace (prefixWord ++ tailWord_7659997) baseStart_7659997 baseEnd_7659997 := by
    simpa [prefixWord, tailWord_7659997, baseEnd_7659997] using wordTrace_append hprefix tailTrace_7659997
  have hstable : (prefixWord ++ tailWord_7659997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7659997).length < 2 ^ (prefixWord ++ tailWord_7659997).sum := by decide
  have hdescent : baseEnd_7659997 < baseStart_7659997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7659997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660020 : List Nat := [2, 6, 15]
def baseStart_7660020 : Nat := 118140960795 + 7660020 * 2 ^ 59
def prefixEnd_7660020 : Nat := 4983230072969 + 3 ^ 40 * 7660020 * 2
def baseEnd_7660020 : Nat := 599492772908584875815

theorem tailTrace_7660020 : CollatzResearch.WordTrace tailWord_7660020 prefixEnd_7660020 599492772908584875815 := by
  unfold tailWord_7660020
  simp only [CollatzResearch.WordTrace]
  refine ⟨139691940854531621053908757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186255921139375494738545009 139691940854531621053908757)
  ·
    refine ⟨6548059727556169736901973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 139691940854531621053908757 6548059727556169736901973)
    ·
      refine ⟨599492772908584875815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 6548059727556169736901973 599492772908584875815)
      ·
        rfl

theorem cell23_7660020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 15].length) (baseStart_7660020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660020 prefixEnd_7660020 := by exact prefixLift 7660020
  have htrace : WordTrace (prefixWord ++ tailWord_7660020) baseStart_7660020 baseEnd_7660020 := by
    simpa [prefixWord, tailWord_7660020, baseEnd_7660020] using wordTrace_append hprefix tailTrace_7660020
  have hstable : (prefixWord ++ tailWord_7660020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660020).length < 2 ^ (prefixWord ++ tailWord_7660020).sum := by decide
  have hdescent : baseEnd_7660020 < baseStart_7660020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660031 : List Nat := [1, 1, 2, 2, 1, 2, 5, 4, 1, 2, 2]
def baseStart_7660031 : Nat := 118140960795 + 7660031 * 2 ^ 59
def prefixEnd_7660031 : Nat := 4983230072969 + 3 ^ 40 * 7660031 * 2
def baseEnd_7660031 : Nat := 3933277731340424827184665

theorem tailTrace_7660031 : CollatzResearch.WordTrace tailWord_7660031 prefixEnd_7660031 3933277731340424827184665 := by
  unfold tailWord_7660031
  simp only [CollatzResearch.WordTrace]
  refine ⟨279384282912023390986467947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186256188608015593990978631 279384282912023390986467947)
  ·
    refine ⟨419076424368035086479701921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279384282912023390986467947 419076424368035086479701921)
    ·
      refine ⟨314307318276026314859776441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419076424368035086479701921 314307318276026314859776441)
      ·
        refine ⟨235730488707019736144832331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314307318276026314859776441 235730488707019736144832331)
        ·
          refine ⟨353595733060529604217248497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235730488707019736144832331 353595733060529604217248497)
          ·
            refine ⟨265196799795397203162936373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353595733060529604217248497 265196799795397203162936373)
            ·
              refine ⟨24862199980818487796525285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 265196799795397203162936373 24862199980818487796525285)
              ·
                refine ⟨4661662496403466461848491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24862199980818487796525285 4661662496403466461848491)
                ·
                  refine ⟨6992493744605199692772737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4661662496403466461848491 6992493744605199692772737)
                  ·
                    refine ⟨5244370308453899769579553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6992493744605199692772737 5244370308453899769579553)
                    ·
                      refine ⟨3933277731340424827184665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5244370308453899769579553 3933277731340424827184665)
                      ·
                        rfl

theorem cell23_7660031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 1, 2, 2].length) (baseStart_7660031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660031 prefixEnd_7660031 := by exact prefixLift 7660031
  have htrace : WordTrace (prefixWord ++ tailWord_7660031) baseStart_7660031 baseEnd_7660031 := by
    simpa [prefixWord, tailWord_7660031, baseEnd_7660031] using wordTrace_append hprefix tailTrace_7660031
  have hstable : (prefixWord ++ tailWord_7660031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660031).length < 2 ^ (prefixWord ++ tailWord_7660031).sum := by decide
  have hdescent : baseEnd_7660031 < baseStart_7660031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660080 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 2, 6]
def baseStart_7660080 : Nat := 118140960795 + 7660080 * 2 ^ 59
def prefixEnd_7660080 : Nat := 4983230072969 + 3 ^ 40 * 7660080 * 2
def baseEnd_7660080 : Nat := 1311100963964165045157313

theorem tailTrace_7660080 : CollatzResearch.WordTrace tailWord_7660080 prefixEnd_7660080 1311100963964165045157313 := by
  unfold tailWord_7660080
  simp only [CollatzResearch.WordTrace]
  refine ⟨139693035044422936177500847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186257380059230581570001129 139693035044422936177500847)
  ·
    refine ⟨209539552566634404266251271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139693035044422936177500847 209539552566634404266251271)
    ·
      refine ⟨314309328849951606399376907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209539552566634404266251271 314309328849951606399376907)
      ·
        refine ⟨471463993274927409599065361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314309328849951606399376907 471463993274927409599065361)
        ·
          refine ⟨353597994956195557199299021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471463993274927409599065361 353597994956195557199299021)
          ·
            refine ⟨132599248108573333949737133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353597994956195557199299021 132599248108573333949737133)
            ·
              refine ⟨49724718040715000231151425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132599248108573333949737133 49724718040715000231151425)
              ·
                refine ⟨37293538530536250173363569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49724718040715000231151425 37293538530536250173363569)
                ·
                  refine ⟨27970153897902187630022677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37293538530536250173363569 27970153897902187630022677)
                  ·
                    refine ⟨1311100963964165045157313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27970153897902187630022677 1311100963964165045157313)
                    ·
                      rfl

theorem cell23_7660080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 2, 6].length) (baseStart_7660080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660080 prefixEnd_7660080 := by exact prefixLift 7660080
  have htrace : WordTrace (prefixWord ++ tailWord_7660080) baseStart_7660080 baseEnd_7660080 := by
    simpa [prefixWord, tailWord_7660080, baseEnd_7660080] using wordTrace_append hprefix tailTrace_7660080
  have hstable : (prefixWord ++ tailWord_7660080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660080).length < 2 ^ (prefixWord ++ tailWord_7660080).sum := by decide
  have hdescent : baseEnd_7660080 < baseStart_7660080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660097 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 2, 6]
def baseStart_7660097 : Nat := 118140960795 + 7660097 * 2 ^ 59
def prefixEnd_7660097 : Nat := 4983230072969 + 3 ^ 40 * 7660097 * 2
def baseEnd_7660097 : Nat := 1311103873687873856319787

theorem tailTrace_7660097 : CollatzResearch.WordTrace tailWord_7660097 prefixEnd_7660097 1311103873687873856319787 := by
  unfold tailWord_7660097
  simp only [CollatzResearch.WordTrace]
  refine ⟨279386690129784284258370545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186257793419856189505580363 279386690129784284258370545)
  ·
    refine ⟨209540017597338213193777909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279386690129784284258370545 209540017597338213193777909)
    ·
      refine ⟨19644376649750457486916679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209540017597338213193777909 19644376649750457486916679)
      ·
        refine ⟨29466564974625686230375019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19644376649750457486916679 29466564974625686230375019)
        ·
          refine ⟨44199847461938529345562529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29466564974625686230375019 44199847461938529345562529)
          ·
            refine ⟨33149885596453897009171897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44199847461938529345562529 33149885596453897009171897)
            ·
              refine ⟨24862414197340422756878923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33149885596453897009171897 24862414197340422756878923)
              ·
                refine ⟨37293621296010634135318385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24862414197340422756878923 37293621296010634135318385)
                ·
                  refine ⟨27970215972007975601488789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37293621296010634135318385 27970215972007975601488789)
                  ·
                    refine ⟨1311103873687873856319787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27970215972007975601488789 1311103873687873856319787)
                    ·
                      rfl

theorem cell23_7660097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_7660097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660097 prefixEnd_7660097 := by exact prefixLift 7660097
  have htrace : WordTrace (prefixWord ++ tailWord_7660097) baseStart_7660097 baseEnd_7660097 := by
    simpa [prefixWord, tailWord_7660097, baseEnd_7660097] using wordTrace_append hprefix tailTrace_7660097
  have hstable : (prefixWord ++ tailWord_7660097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660097).length < 2 ^ (prefixWord ++ tailWord_7660097).sum := by decide
  have hdescent : baseEnd_7660097 < baseStart_7660097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660124 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_7660124 : Nat := 118140960795 + 7660124 * 2 ^ 59
def prefixEnd_7660124 : Nat := 4983230072969 + 3 ^ 40 * 7660124 * 2
def baseEnd_7660124 : Nat := 3933325485041292963321737

theorem tailTrace_7660124 : CollatzResearch.WordTrace tailWord_7660124 prefixEnd_7660124 3933325485041292963321737 := by
  unfold tailWord_7660124
  simp only [CollatzResearch.WordTrace]
  refine ⟨139693837450343233934801713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186258449933790978579735617 139693837450343233934801713)
  ·
    refine ⟨104770378087757425451101285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139693837450343233934801713 104770378087757425451101285)
    ·
      refine ⟨19644445891454517272081491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104770378087757425451101285 19644445891454517272081491)
      ·
        refine ⟨29466668837181775908122237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19644445891454517272081491 29466668837181775908122237)
        ·
          refine ⟨11050000813943165965545839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29466668837181775908122237 11050000813943165965545839)
          ·
            refine ⟨16575001220914748948318759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11050000813943165965545839 16575001220914748948318759)
            ·
              refine ⟨24862501831372123422478139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16575001220914748948318759 24862501831372123422478139)
              ·
                refine ⟨37293752747058185133717209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24862501831372123422478139 37293752747058185133717209)
                ·
                  refine ⟨27970314560293638850287907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37293752747058185133717209 27970314560293638850287907)
                  ·
                    refine ⟨41955471840440458275431861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27970314560293638850287907 41955471840440458275431861)
                    ·
                      refine ⟨3933325485041292963321737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41955471840440458275431861 3933325485041292963321737)
                      ·
                        rfl

theorem cell23_7660124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_7660124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660124 prefixEnd_7660124 := by exact prefixLift 7660124
  have htrace : WordTrace (prefixWord ++ tailWord_7660124) baseStart_7660124 baseEnd_7660124 := by
    simpa [prefixWord, tailWord_7660124, baseEnd_7660124] using wordTrace_append hprefix tailTrace_7660124
  have hstable : (prefixWord ++ tailWord_7660124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660124).length < 2 ^ (prefixWord ++ tailWord_7660124).sum := by decide
  have hdescent : baseEnd_7660124 < baseStart_7660124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660144 : List Nat := [2, 1, 1, 1, 7, 2, 1, 1, 7]
def baseStart_7660144 : Nat := 118140960795 + 7660144 * 2 ^ 59
def prefixEnd_7660144 : Nat := 4983230072969 + 3 ^ 40 * 7660144 * 2
def baseEnd_7660144 : Nat := 437037306072709209452405

theorem tailTrace_7660144 : CollatzResearch.WordTrace tailWord_7660144 prefixEnd_7660144 437037306072709209452405 := by
  unfold tailWord_7660144
  simp only [CollatzResearch.WordTrace]
  refine ⟨139694202180307005642665743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186258936240409340856887657 139694202180307005642665743)
  ·
    refine ⟨209541303270460508463998615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139694202180307005642665743 209541303270460508463998615)
    ·
      refine ⟨314311954905690762695997923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209541303270460508463998615 314311954905690762695997923)
      ·
        refine ⟨471467932358536144043996885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314311954905690762695997923 471467932358536144043996885)
        ·
          refine ⟨11050029664653190876031177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 471467932358536144043996885 11050029664653190876031177)
          ·
            refine ⟨8287522248489893157023383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11050029664653190876031177 8287522248489893157023383)
            ·
              refine ⟨12431283372734839735535075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8287522248489893157023383 12431283372734839735535075)
              ·
                refine ⟨18646925059102259603302613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12431283372734839735535075 18646925059102259603302613)
                ·
                  refine ⟨437037306072709209452405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18646925059102259603302613 437037306072709209452405)
                  ·
                    rfl

theorem cell23_7660144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 7].length) (baseStart_7660144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660144 prefixEnd_7660144 := by exact prefixLift 7660144
  have htrace : WordTrace (prefixWord ++ tailWord_7660144) baseStart_7660144 baseEnd_7660144 := by
    simpa [prefixWord, tailWord_7660144, baseEnd_7660144] using wordTrace_append hprefix tailTrace_7660144
  have hstable : (prefixWord ++ tailWord_7660144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660144).length < 2 ^ (prefixWord ++ tailWord_7660144).sum := by decide
  have hdescent : baseEnd_7660144 < baseStart_7660144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660174 : List Nat := [4, 1, 1, 3, 1, 1, 4, 1, 2, 5]
def baseStart_7660174 : Nat := 118140960795 + 7660174 * 2 ^ 59
def prefixEnd_7660174 : Nat := 4983230072969 + 3 ^ 40 * 7660174 * 2
def baseEnd_7660174 : Nat := 1311117053024672589232169

theorem tailTrace_7660174 : CollatzResearch.WordTrace tailWord_7660174 prefixEnd_7660174 1311117053024672589232169 := by
  unfold tailWord_7660174
  simp only [CollatzResearch.WordTrace]
  refine ⟨34923687318813165801115447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186259665700336884272615717 34923687318813165801115447)
  ·
    refine ⟨52385530978219748701673171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34923687318813165801115447 52385530978219748701673171)
    ·
      refine ⟨78578296467329623052509757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52385530978219748701673171 78578296467329623052509757)
      ·
        refine ⟨29466861175248608644691159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78578296467329623052509757 29466861175248608644691159)
        ·
          refine ⟨44200291762872912967036739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29466861175248608644691159 44200291762872912967036739)
          ·
            refine ⟨66300437644309369450555109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44200291762872912967036739 66300437644309369450555109)
            ·
              refine ⟨12431332058308006771979083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66300437644309369450555109 12431332058308006771979083)
              ·
                refine ⟨18646998087462010157968625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12431332058308006771979083 18646998087462010157968625)
                ·
                  refine ⟨13985248565596507618476469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18646998087462010157968625 13985248565596507618476469)
                  ·
                    refine ⟨1311117053024672589232169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13985248565596507618476469 1311117053024672589232169)
                    ·
                      rfl

theorem cell23_7660174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_7660174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660174 prefixEnd_7660174 := by exact prefixLift 7660174
  have htrace : WordTrace (prefixWord ++ tailWord_7660174) baseStart_7660174 baseEnd_7660174 := by
    simpa [prefixWord, tailWord_7660174, baseEnd_7660174] using wordTrace_append hprefix tailTrace_7660174
  have hstable : (prefixWord ++ tailWord_7660174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660174).length < 2 ^ (prefixWord ++ tailWord_7660174).sum := by decide
  have hdescent : baseEnd_7660174 < baseStart_7660174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660197 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 3, 4, 3]
def baseStart_7660197 : Nat := 118140960795 + 7660197 * 2 ^ 59
def prefixEnd_7660197 : Nat := 4983230072969 + 3 ^ 40 * 7660197 * 2
def baseEnd_7660197 : Nat := 3933362969129071177708901

theorem tailTrace_7660197 : CollatzResearch.WordTrace tailWord_7660197 prefixEnd_7660197 3933362969129071177708901 := by
  unfold tailWord_7660197
  simp only [CollatzResearch.WordTrace]
  refine ⟨279390337429422001337010845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186260224952948000891340563 279390337429422001337010845)
  ·
    refine ⟨104771376536033250501379067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279390337429422001337010845 104771376536033250501379067)
    ·
      refine ⟨157157064804049875752068601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104771376536033250501379067 157157064804049875752068601)
      ·
        refine ⟨117867798603037406814051451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157157064804049875752068601 117867798603037406814051451)
        ·
          refine ⟨176801697904556110221077177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117867798603037406814051451 176801697904556110221077177)
          ·
            refine ⟨132601273428417082665807883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176801697904556110221077177 132601273428417082665807883)
            ·
              refine ⟨198901910142625623998711825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132601273428417082665807883 198901910142625623998711825)
              ·
                refine ⟨149176432606969217999033869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198901910142625623998711825 149176432606969217999033869)
                ·
                  refine ⟨55941162227613456749637701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149176432606969217999033869 55941162227613456749637701)
                  ·
                    refine ⟨10488967917677523140557069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55941162227613456749637701 10488967917677523140557069)
                    ·
                      refine ⟨3933362969129071177708901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10488967917677523140557069 3933362969129071177708901)
                      ·
                        rfl

theorem cell23_7660197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_7660197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660197 prefixEnd_7660197 := by exact prefixLift 7660197
  have htrace : WordTrace (prefixWord ++ tailWord_7660197) baseStart_7660197 baseEnd_7660197 := by
    simpa [prefixWord, tailWord_7660197, baseEnd_7660197] using wordTrace_append hprefix tailTrace_7660197
  have hstable : (prefixWord ++ tailWord_7660197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660197).length < 2 ^ (prefixWord ++ tailWord_7660197).sum := by decide
  have hdescent : baseEnd_7660197 < baseStart_7660197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660225 : List Nat := [1, 2, 6, 2, 2, 1, 1, 1, 2, 5]
def baseStart_7660225 : Nat := 118140960795 + 7660225 * 2 ^ 59
def prefixEnd_7660225 : Nat := 4983230072969 + 3 ^ 40 * 7660225 * 2
def baseEnd_7660225 : Nat := 1311125782195799022719591

theorem tailTrace_7660225 : CollatzResearch.WordTrace tailWord_7660225 prefixEnd_7660225 1311125782195799022719591 := by
  unfold tailWord_7660225
  simp only [CollatzResearch.WordTrace]
  refine ⟨279391358673320562119030129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186260905782213708079353419 279391358673320562119030129)
  ·
    refine ⟨209543519004990421589272597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279391358673320562119030129 209543519004990421589272597)
    ·
      refine ⟨9822352453358926011997153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 209543519004990421589272597 9822352453358926011997153)
      ·
        refine ⟨7366764340019194508997865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9822352453358926011997153 7366764340019194508997865)
        ·
          refine ⟨5525073255014395881748399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7366764340019194508997865 5525073255014395881748399)
          ·
            refine ⟨8287609882521593822622599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5525073255014395881748399 8287609882521593822622599)
            ·
              refine ⟨12431414823782390733933899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8287609882521593822622599 12431414823782390733933899)
              ·
                refine ⟨18647122235673586100900849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12431414823782390733933899 18647122235673586100900849)
                ·
                  refine ⟨13985341676755189575675637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18647122235673586100900849 13985341676755189575675637)
                  ·
                    refine ⟨1311125782195799022719591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13985341676755189575675637 1311125782195799022719591)
                    ·
                      rfl

theorem cell23_7660225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_7660225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660225 prefixEnd_7660225 := by exact prefixLift 7660225
  have htrace : WordTrace (prefixWord ++ tailWord_7660225) baseStart_7660225 baseEnd_7660225 := by
    simpa [prefixWord, tailWord_7660225, baseEnd_7660225] using wordTrace_append hprefix tailTrace_7660225
  have hstable : (prefixWord ++ tailWord_7660225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660225).length < 2 ^ (prefixWord ++ tailWord_7660225).sum := by decide
  have hdescent : baseEnd_7660225 < baseStart_7660225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660238 : List Nat := [4, 1, 1, 1, 3, 3, 2, 3, 1, 4]
def baseStart_7660238 : Nat := 118140960795 + 7660238 * 2 ^ 59
def prefixEnd_7660238 : Nat := 4983230072969 + 3 ^ 40 * 7660238 * 2
def baseEnd_7660238 : Nat := 1311128007278635172432071

theorem tailTrace_7660238 : CollatzResearch.WordTrace tailWord_7660238 prefixEnd_7660238 1311128007278635172432071 := by
  unfold tailWord_7660238
  simp only [CollatzResearch.WordTrace]
  refine ⟨34923979102784183167406671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186261221881515643559502245 34923979102784183167406671)
  ·
    refine ⟨52385968654176274751110007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34923979102784183167406671 52385968654176274751110007)
    ·
      refine ⟨78578952981264412126665011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52385968654176274751110007 78578952981264412126665011)
      ·
        refine ⟨117868429471896618189997517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78578952981264412126665011 117868429471896618189997517)
        ·
          refine ⟨44200661051961231821249069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117868429471896618189997517 44200661051961231821249069)
          ·
            refine ⟨16575247894485461932968401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44200661051961231821249069 16575247894485461932968401)
            ·
              refine ⟨12431435920864096449726301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16575247894485461932968401 12431435920864096449726301)
              ·
                refine ⟨4661788470324036168647363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12431435920864096449726301 4661788470324036168647363)
                ·
                  refine ⟨6992682705486054252971045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4661788470324036168647363 6992682705486054252971045)
                  ·
                    refine ⟨1311128007278635172432071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6992682705486054252971045 1311128007278635172432071)
                    ·
                      rfl

theorem cell23_7660238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_7660238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660238 prefixEnd_7660238 := by exact prefixLift 7660238
  have htrace : WordTrace (prefixWord ++ tailWord_7660238) baseStart_7660238 baseEnd_7660238 := by
    simpa [prefixWord, tailWord_7660238, baseEnd_7660238] using wordTrace_append hprefix tailTrace_7660238
  have hstable : (prefixWord ++ tailWord_7660238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660238).length < 2 ^ (prefixWord ++ tailWord_7660238).sum := by decide
  have hdescent : baseEnd_7660238 < baseStart_7660238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660261 : List Nat := [1, 3, 1, 4, 1, 2, 1, 3, 3, 1, 3]
def baseStart_7660261 : Nat := 118140960795 + 7660261 * 2 ^ 59
def prefixEnd_7660261 : Nat := 4983230072969 + 3 ^ 40 * 7660261 * 2
def baseEnd_7660261 : Nat := 3933395831890958927308607

theorem tailTrace_7660261 : CollatzResearch.WordTrace tailWord_7660261 prefixEnd_7660261 3933395831890958927308607 := by
  unfold tailWord_7660261
  simp only [CollatzResearch.WordTrace]
  refine ⟨279392671701190140267340637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186261781134126760178227091 279392671701190140267340637)
  ·
    refine ⟨104772251887946302600252739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279392671701190140267340637 104772251887946302600252739)
    ·
      refine ⟨157158377831919453900379109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104772251887946302600252739 157158377831919453900379109)
      ·
        refine ⟨29467195843484897606321083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157158377831919453900379109 29467195843484897606321083)
        ·
          refine ⟨44200793765227346409481625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29467195843484897606321083 44200793765227346409481625)
          ·
            refine ⟨33150595323920509807111219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44200793765227346409481625 33150595323920509807111219)
            ·
              refine ⟨49725892985880764710666829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33150595323920509807111219 49725892985880764710666829)
              ·
                refine ⟨18647209869705286766500061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49725892985880764710666829 18647209869705286766500061)
                ·
                  refine ⟨6992703701139482537437523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18647209869705286766500061 6992703701139482537437523)
                  ·
                    refine ⟨10489055551709223806156285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6992703701139482537437523 10489055551709223806156285)
                    ·
                      refine ⟨3933395831890958927308607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10489055551709223806156285 3933395831890958927308607)
                      ·
                        rfl

theorem cell23_7660261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_7660261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660261 prefixEnd_7660261 := by exact prefixLift 7660261
  have htrace : WordTrace (prefixWord ++ tailWord_7660261) baseStart_7660261 baseEnd_7660261 := by
    simpa [prefixWord, tailWord_7660261, baseEnd_7660261] using wordTrace_append hprefix tailTrace_7660261
  have hstable : (prefixWord ++ tailWord_7660261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660261).length < 2 ^ (prefixWord ++ tailWord_7660261).sum := by decide
  have hdescent : baseEnd_7660261 < baseStart_7660261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660287 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 5]
def baseStart_7660287 : Nat := 118140960795 + 7660287 * 2 ^ 59
def prefixEnd_7660287 : Nat := 4983230072969 + 3 ^ 40 * 7660287 * 2
def baseEnd_7660287 : Nat := 3933409182387975825583487

theorem tailTrace_7660287 : CollatzResearch.WordTrace tailWord_7660287 prefixEnd_7660287 3933409182387975825583487 := by
  unfold tailWord_7660287
  simp only [CollatzResearch.WordTrace]
  refine ⟨279393619999095946707787115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186262413332730631138524743 279393619999095946707787115)
  ·
    refine ⟨419090429998643920061680673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279393619999095946707787115 419090429998643920061680673)
    ·
      refine ⟨314317822498982940046260505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419090429998643920061680673 314317822498982940046260505)
      ·
        refine ⟨235738366874237205034695379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314317822498982940046260505 235738366874237205034695379)
        ·
          refine ⟨353607550311355807552043069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235738366874237205034695379 353607550311355807552043069)
          ·
            refine ⟨132602831366758427832016151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353607550311355807552043069 132602831366758427832016151)
            ·
              refine ⟨198904247050137641748024227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132602831366758427832016151 198904247050137641748024227)
              ·
                refine ⟨298356370575206462622036341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198904247050137641748024227 298356370575206462622036341)
                ·
                  refine ⟨27970909741425605870815907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 298356370575206462622036341 27970909741425605870815907)
                  ·
                    refine ⟨41956364612138408806223861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27970909741425605870815907 41956364612138408806223861)
                    ·
                      refine ⟨3933409182387975825583487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41956364612138408806223861 3933409182387975825583487)
                      ·
                        rfl

theorem cell23_7660287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_7660287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660287 prefixEnd_7660287 := by exact prefixLift 7660287
  have htrace : WordTrace (prefixWord ++ tailWord_7660287) baseStart_7660287 baseEnd_7660287 := by
    simpa [prefixWord, tailWord_7660287, baseEnd_7660287] using wordTrace_append hprefix tailTrace_7660287
  have hstable : (prefixWord ++ tailWord_7660287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660287).length < 2 ^ (prefixWord ++ tailWord_7660287).sum := by decide
  have hdescent : baseEnd_7660287 < baseStart_7660287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660295 : List Nat := [1, 1, 4, 4, 1, 1, 3, 3, 1, 1, 3]
def baseStart_7660295 : Nat := 118140960795 + 7660295 * 2 ^ 59
def prefixEnd_7660295 : Nat := 4983230072969 + 3 ^ 40 * 7660295 * 2
def baseEnd_7660295 : Nat := 3933413290233211794283451

theorem tailTrace_7660295 : CollatzResearch.WordTrace tailWord_7660295 prefixEnd_7660295 3933413290233211794283451 := by
  unfold tailWord_7660295
  simp only [CollatzResearch.WordTrace]
  refine ⟨279393911783066964074078339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186262607855377976049385559 279393911783066964074078339)
  ·
    refine ⟨419090867674600446111117509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279393911783066964074078339 419090867674600446111117509)
    ·
      refine ⟨78579537688987583645834533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 419090867674600446111117509 78579537688987583645834533)
      ·
        refine ⟨14733663316685171933593975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78579537688987583645834533 14733663316685171933593975)
        ·
          refine ⟨22100494975027757900390963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14733663316685171933593975 22100494975027757900390963)
          ·
            refine ⟨33150742462541636850586445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22100494975027757900390963 33150742462541636850586445)
            ·
              refine ⟨12431528423453113818969917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33150742462541636850586445 12431528423453113818969917)
              ·
                refine ⟨4661823158794917682113719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12431528423453113818969917 4661823158794917682113719)
                ·
                  refine ⟨6992734738192376523170579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4661823158794917682113719 6992734738192376523170579)
                  ·
                    refine ⟨10489102107288564784755869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6992734738192376523170579 10489102107288564784755869)
                    ·
                      refine ⟨3933413290233211794283451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10489102107288564784755869 3933413290233211794283451)
                      ·
                        rfl

theorem cell23_7660295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_7660295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660295 prefixEnd_7660295 := by exact prefixLift 7660295
  have htrace : WordTrace (prefixWord ++ tailWord_7660295) baseStart_7660295 baseEnd_7660295 := by
    simpa [prefixWord, tailWord_7660295, baseEnd_7660295] using wordTrace_append hprefix tailTrace_7660295
  have hstable : (prefixWord ++ tailWord_7660295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660295).length < 2 ^ (prefixWord ++ tailWord_7660295).sum := by decide
  have hdescent : baseEnd_7660295 < baseStart_7660295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660351 : List Nat := [1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 3]
def baseStart_7660351 : Nat := 118140960795 + 7660351 * 2 ^ 59
def prefixEnd_7660351 : Nat := 4983230072969 + 3 ^ 40 * 7660351 * 2
def baseEnd_7660351 : Nat := 3933442045149863575183193

theorem tailTrace_7660351 : CollatzResearch.WordTrace tailWord_7660351 prefixEnd_7660351 3933442045149863575183193 := by
  unfold tailWord_7660351
  simp only [CollatzResearch.WordTrace]
  refine ⟨279395954270864085638116907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186263969513909390425411271 279395954270864085638116907)
  ·
    refine ⟨419093931406296128457175361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279395954270864085638116907 419093931406296128457175361)
    ·
      refine ⟨314320448554722096342881521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419093931406296128457175361 314320448554722096342881521)
      ·
        refine ⟨235740336416041572257161141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314320448554722096342881521 235740336416041572257161141)
        ·
          refine ⟨22100656539003897399108857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 235740336416041572257161141 22100656539003897399108857)
          ·
            refine ⟨16575492404252923049331643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22100656539003897399108857 16575492404252923049331643)
            ·
              refine ⟨24863238606379384573997465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16575492404252923049331643 24863238606379384573997465)
              ·
                refine ⟨18647428954784538430498099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24863238606379384573997465 18647428954784538430498099)
                ·
                  refine ⟨27971143432176807645747149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18647428954784538430498099 27971143432176807645747149)
                  ·
                    refine ⟨10489178787066302867155181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27971143432176807645747149 10489178787066302867155181)
                    ·
                      refine ⟨3933442045149863575183193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10489178787066302867155181 3933442045149863575183193)
                      ·
                        rfl

theorem cell23_7660351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_7660351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660351 prefixEnd_7660351 := by exact prefixLift 7660351
  have htrace : WordTrace (prefixWord ++ tailWord_7660351) baseStart_7660351 baseEnd_7660351 := by
    simpa [prefixWord, tailWord_7660351, baseEnd_7660351] using wordTrace_append hprefix tailTrace_7660351
  have hstable : (prefixWord ++ tailWord_7660351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660351).length < 2 ^ (prefixWord ++ tailWord_7660351).sum := by decide
  have hdescent : baseEnd_7660351 < baseStart_7660351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660358 : List Nat := [6, 1, 1, 2, 3, 10]
def baseStart_7660358 : Nat := 118140960795 + 7660358 * 2 ^ 59
def prefixEnd_7660358 : Nat := 4983230072969 + 3 ^ 40 * 7660358 * 2
def baseEnd_7660358 : Nat := 16187019092652037233727

theorem tailTrace_7660358 : CollatzResearch.WordTrace tailWord_7660358 prefixEnd_7660358 16187019092652037233727 := by
  unfold tailWord_7660358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8731131549432460182300679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 186264139721225817222414485 8731131549432460182300679)
  ·
    refine ⟨13096697324148690273451019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8731131549432460182300679 13096697324148690273451019)
    ·
      refine ⟨19645045986223035410176529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13096697324148690273451019 19645045986223035410176529)
      ·
        refine ⟨14733784489667276557632397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19645045986223035410176529 14733784489667276557632397)
        ·
          refine ⟨5525169183625228709112149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14733784489667276557632397 5525169183625228709112149)
          ·
            refine ⟨16187019092652037233727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5525169183625228709112149 16187019092652037233727)
            ·
              rfl

theorem cell23_7660358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 10].length) (baseStart_7660358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660358 prefixEnd_7660358 := by exact prefixLift 7660358
  have htrace : WordTrace (prefixWord ++ tailWord_7660358) baseStart_7660358 baseEnd_7660358 := by
    simpa [prefixWord, tailWord_7660358, baseEnd_7660358] using wordTrace_append hprefix tailTrace_7660358
  have hstable : (prefixWord ++ tailWord_7660358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660358).length < 2 ^ (prefixWord ++ tailWord_7660358).sum := by decide
  have hdescent : baseEnd_7660358 < baseStart_7660358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660367 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 5, 8]
def baseStart_7660367 : Nat := 118140960795 + 7660367 * 2 ^ 59
def prefixEnd_7660367 : Nat := 4983230072969 + 3 ^ 40 * 7660367 * 2
def baseEnd_7660367 : Nat := 1311150086946778504194373

theorem tailTrace_7660367 : CollatzResearch.WordTrace tailWord_7660367 prefixEnd_7660367 1311150086946778504194373 := by
  unfold tailWord_7660367
  simp only [CollatzResearch.WordTrace]
  refine ⟨279396537838806120370699355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186264358559204080247132903 279396537838806120370699355)
  ·
    refine ⟨419094806758209180556049033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279396537838806120370699355 419094806758209180556049033)
    ·
      refine ⟨314321105068656885417036775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419094806758209180556049033 314321105068656885417036775)
      ·
        refine ⟨471481657602985328125555163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314321105068656885417036775 471481657602985328125555163)
        ·
          refine ⟨707222486404477992188332745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471481657602985328125555163 707222486404477992188332745)
          ·
            refine ⟨530416864803358494141249559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707222486404477992188332745 530416864803358494141249559)
            ·
              refine ⟨795625297205037741211874339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530416864803358494141249559 795625297205037741211874339)
              ·
                refine ⟨1193437945807556611817811509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795625297205037741211874339 1193437945807556611817811509)
                ·
                  refine ⟨111884807419458432357919829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1193437945807556611817811509 111884807419458432357919829)
                  ·
                    refine ⟨1311150086946778504194373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111884807419458432357919829 1311150086946778504194373)
                    ·
                      rfl

theorem cell23_7660367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 8].length) (baseStart_7660367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660367 prefixEnd_7660367 := by exact prefixLift 7660367
  have htrace : WordTrace (prefixWord ++ tailWord_7660367) baseStart_7660367 baseEnd_7660367 := by
    simpa [prefixWord, tailWord_7660367, baseEnd_7660367] using wordTrace_append hprefix tailTrace_7660367
  have hstable : (prefixWord ++ tailWord_7660367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660367).length < 2 ^ (prefixWord ++ tailWord_7660367).sum := by decide
  have hdescent : baseEnd_7660367 < baseStart_7660367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660369 : List Nat := [1, 2, 2, 1, 6, 2, 2, 2, 1, 2, 2]
def baseStart_7660369 : Nat := 118140960795 + 7660369 * 2 ^ 59
def prefixEnd_7660369 : Nat := 4983230072969 + 3 ^ 40 * 7660369 * 2
def baseEnd_7660369 : Nat := 3933451287801644504758111

theorem tailTrace_7660369 : CollatzResearch.WordTrace tailWord_7660369 prefixEnd_7660369 3933451287801644504758111 := by
  unfold tailWord_7660369
  simp only [CollatzResearch.WordTrace]
  refine ⟨279396610784798874712272161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186264407189865916474848107 279396610784798874712272161)
  ·
    refine ⟨209547458088599156034204121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279396610784798874712272161 209547458088599156034204121)
    ·
      refine ⟨157160593566449367025653091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209547458088599156034204121 157160593566449367025653091)
      ·
        refine ⟨235740890349674050538479637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157160593566449367025653091 235740890349674050538479637)
        ·
          refine ⟨11050354235140971118991233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 235740890349674050538479637 11050354235140971118991233)
          ·
            refine ⟨8287765676355728339243425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11050354235140971118991233 8287765676355728339243425)
            ·
              refine ⟨6215824257266796254432569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8287765676355728339243425 6215824257266796254432569)
              ·
                refine ⟨4661868192950097190824427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6215824257266796254432569 4661868192950097190824427)
                ·
                  refine ⟨6992802289425145786236641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4661868192950097190824427 6992802289425145786236641)
                  ·
                    refine ⟨5244601717068859339677481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6992802289425145786236641 5244601717068859339677481)
                    ·
                      refine ⟨3933451287801644504758111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5244601717068859339677481 3933451287801644504758111)
                      ·
                        rfl

theorem cell23_7660369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 1, 2, 2].length) (baseStart_7660369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660369 prefixEnd_7660369 := by exact prefixLift 7660369
  have htrace : WordTrace (prefixWord ++ tailWord_7660369) baseStart_7660369 baseEnd_7660369 := by
    simpa [prefixWord, tailWord_7660369, baseEnd_7660369] using wordTrace_append hprefix tailTrace_7660369
  have hstable : (prefixWord ++ tailWord_7660369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660369).length < 2 ^ (prefixWord ++ tailWord_7660369).sum := by decide
  have hdescent : baseEnd_7660369 < baseStart_7660369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660384 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 2, 6]
def baseStart_7660384 : Nat := 118140960795 + 7660384 * 2 ^ 59
def prefixEnd_7660384 : Nat := 4983230072969 + 3 ^ 40 * 7660384 * 2
def baseEnd_7660384 : Nat := 1311152996670487315356847

theorem tailTrace_7660384 : CollatzResearch.WordTrace tailWord_7660384 prefixEnd_7660384 1311152996670487315356847 := by
  unfold tailWord_7660384
  simp only [CollatzResearch.WordTrace]
  refine ⟨139698578939872266137034103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186264771919829688182712137 139698578939872266137034103)
  ·
    refine ⟨209547868409808399205551155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139698578939872266137034103 209547868409808399205551155)
    ·
      refine ⟨314321802614712598808326733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209547868409808399205551155 314321802614712598808326733)
      ·
        refine ⟨117870675980517224553122525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314321802614712598808326733 117870675980517224553122525)
        ·
          refine ⟨44201503492693959207420947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117870675980517224553122525 44201503492693959207420947)
          ·
            refine ⟨66302255239040938811131421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44201503492693959207420947 66302255239040938811131421)
            ·
              refine ⟨24863345714640352054174283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66302255239040938811131421 24863345714640352054174283)
              ·
                refine ⟨37295018571960528081261425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24863345714640352054174283 37295018571960528081261425)
                ·
                  refine ⟨27971263928970396060946069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37295018571960528081261425 27971263928970396060946069)
                  ·
                    refine ⟨1311152996670487315356847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27971263928970396060946069 1311152996670487315356847)
                    ·
                      rfl

theorem cell23_7660384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 2, 6].length) (baseStart_7660384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660384 prefixEnd_7660384 := by exact prefixLift 7660384
  have htrace : WordTrace (prefixWord ++ tailWord_7660384) baseStart_7660384 baseEnd_7660384 := by
    simpa [prefixWord, tailWord_7660384, baseEnd_7660384] using wordTrace_append hprefix tailTrace_7660384
  have hstable : (prefixWord ++ tailWord_7660384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660384).length < 2 ^ (prefixWord ++ tailWord_7660384).sum := by decide
  have hdescent : baseEnd_7660384 < baseStart_7660384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660425 : List Nat := [1, 2, 1, 1, 5, 2, 3, 2, 2, 2, 2]
def baseStart_7660425 : Nat := 118140960795 + 7660425 * 2 ^ 59
def prefixEnd_7660425 : Nat := 4983230072969 + 3 ^ 40 * 7660425 * 2
def baseEnd_7660425 : Nat := 3933480042718296285657853

theorem tailTrace_7660425 : CollatzResearch.WordTrace tailWord_7660425 prefixEnd_7660425 3933480042718296285657853 := by
  unfold tailWord_7660425
  simp only [CollatzResearch.WordTrace]
  refine ⟨279398653272595996276310729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186265768848397330850873819 279398653272595996276310729)
  ·
    refine ⟨209548989954446997207233047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279398653272595996276310729 209548989954446997207233047)
    ·
      refine ⟨314323484931670495810849571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209548989954446997207233047 314323484931670495810849571)
      ·
        refine ⟨471485227397505743716274357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314323484931670495810849571 471485227397505743716274357)
        ·
          refine ⟨44201740068516163473400721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 471485227397505743716274357 44201740068516163473400721)
          ·
            refine ⟨33151305051387122605050541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44201740068516163473400721 33151305051387122605050541)
            ·
              refine ⟨12431739394270170976893953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33151305051387122605050541 12431739394270170976893953)
              ·
                refine ⟨9323804545702628232670465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12431739394270170976893953 9323804545702628232670465)
                ·
                  refine ⟨6992853409276971174502849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9323804545702628232670465 6992853409276971174502849)
                  ·
                    refine ⟨5244640056957728380877137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6992853409276971174502849 5244640056957728380877137)
                    ·
                      refine ⟨3933480042718296285657853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5244640056957728380877137 3933480042718296285657853)
                      ·
                        rfl

theorem cell23_7660425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 2, 2].length) (baseStart_7660425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660425 prefixEnd_7660425 := by exact prefixLift 7660425
  have htrace : WordTrace (prefixWord ++ tailWord_7660425) baseStart_7660425 baseEnd_7660425 := by
    simpa [prefixWord, tailWord_7660425, baseEnd_7660425] using wordTrace_append hprefix tailTrace_7660425
  have hstable : (prefixWord ++ tailWord_7660425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660425).length < 2 ^ (prefixWord ++ tailWord_7660425).sum := by decide
  have hdescent : baseEnd_7660425 < baseStart_7660425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660442 : List Nat := [3, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2]
def baseStart_7660442 : Nat := 118140960795 + 7660442 * 2 ^ 59
def prefixEnd_7660442 : Nat := 4983230072969 + 3 ^ 40 * 7660442 * 2
def baseEnd_7660442 : Nat := 3933488771889422719145275

theorem tailTrace_7660442 : CollatzResearch.WordTrace tailWord_7660442 prefixEnd_7660442 3933488771889422719145275 := by
  unfold tailWord_7660442
  simp only [CollatzResearch.WordTrace]
  refine ⟨69849818328383602044919895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186266182209022938786453053 69849818328383602044919895)
  ·
    refine ⟨104774727492575403067379843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69849818328383602044919895 104774727492575403067379843)
    ·
      refine ⟨157162091238863104601069765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104774727492575403067379843 157162091238863104601069765)
      ·
        refine ⟨29467892107286832112700581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157162091238863104601069765 29467892107286832112700581)
        ·
          refine ⟨5525229770116281021131359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29467892107286832112700581 5525229770116281021131359)
          ·
            refine ⟨8287844655174421531697039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5525229770116281021131359 8287844655174421531697039)
            ·
              refine ⟨12431766982761632297545559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8287844655174421531697039 12431766982761632297545559)
              ·
                refine ⟨18647650474142448446318339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12431766982761632297545559 18647650474142448446318339)
                ·
                  refine ⟨27971475711213672669477509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18647650474142448446318339 27971475711213672669477509)
                  ·
                    refine ⟨5244651695852563625527033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27971475711213672669477509 5244651695852563625527033)
                    ·
                      refine ⟨3933488771889422719145275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5244651695852563625527033 3933488771889422719145275)
                      ·
                        rfl

theorem cell23_7660442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_7660442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660442 prefixEnd_7660442 := by exact prefixLift 7660442
  have htrace : WordTrace (prefixWord ++ tailWord_7660442) baseStart_7660442 baseEnd_7660442 := by
    simpa [prefixWord, tailWord_7660442, baseEnd_7660442] using wordTrace_append hprefix tailTrace_7660442
  have hstable : (prefixWord ++ tailWord_7660442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660442).length < 2 ^ (prefixWord ++ tailWord_7660442).sum := by decide
  have hdescent : baseEnd_7660442 < baseStart_7660442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660451 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 2, 5, 2]
def baseStart_7660451 : Nat := 118140960795 + 7660451 * 2 ^ 59
def prefixEnd_7660451 : Nat := 4983230072969 + 3 ^ 40 * 7660451 * 2
def baseEnd_7660451 : Nat := 3933493393215313183932733

theorem tailTrace_7660451 : CollatzResearch.WordTrace tailWord_7660451 prefixEnd_7660451 3933493393215313183932733 := by
  unfold tailWord_7660451
  simp only [CollatzResearch.WordTrace]
  refine ⟨279399601570501802716757207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186266401047001201811171471 279399601570501802716757207)
  ·
    refine ⟨419099402355752704075135811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279399601570501802716757207 419099402355752704075135811)
    ·
      refine ⟨628649103533629056112703717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419099402355752704075135811 628649103533629056112703717)
      ·
        refine ⟨117871706912555448021131947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 628649103533629056112703717 117871706912555448021131947)
        ·
          refine ⟨176807560368833172031697921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117871706912555448021131947 176807560368833172031697921)
          ·
            refine ⟨132605670276624879023773441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176807560368833172031697921 132605670276624879023773441)
            ·
              refine ⟨99454252707468659267830081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132605670276624879023773441 99454252707468659267830081)
              ·
                refine ⟨74590689530601494450872561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99454252707468659267830081 74590689530601494450872561)
                ·
                  refine ⟨55943017147951120838154421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74590689530601494450872561 55943017147951120838154421)
                  ·
                    refine ⟨5244657857620417578576977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55943017147951120838154421 5244657857620417578576977)
                    ·
                      refine ⟨3933493393215313183932733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5244657857620417578576977 3933493393215313183932733)
                      ·
                        rfl

theorem cell23_7660451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_7660451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660451 prefixEnd_7660451 := by exact prefixLift 7660451
  have htrace : WordTrace (prefixWord ++ tailWord_7660451) baseStart_7660451 baseEnd_7660451 := by
    simpa [prefixWord, tailWord_7660451, baseEnd_7660451] using wordTrace_append hprefix tailTrace_7660451
  have hstable : (prefixWord ++ tailWord_7660451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660451).length < 2 ^ (prefixWord ++ tailWord_7660451).sum := by decide
  have hdescent : baseEnd_7660451 < baseStart_7660451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660465 : List Nat := [1, 2, 2, 4, 3, 2, 1, 3, 5]
def baseStart_7660465 : Nat := 118140960795 + 7660465 * 2 ^ 59
def prefixEnd_7660465 : Nat := 4983230072969 + 3 ^ 40 * 7660465 * 2
def baseEnd_7660465 : Nat := 437055620216052903239741

theorem tailTrace_7660465 : CollatzResearch.WordTrace tailWord_7660465 prefixEnd_7660465 437055620216052903239741 := by
  unfold tailWord_7660465
  simp only [CollatzResearch.WordTrace]
  refine ⟨279400112192451083107766849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186266741461634055405177899 279400112192451083107766849)
  ·
    refine ⟨209550084144338312330825137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279400112192451083107766849 209550084144338312330825137)
    ·
      refine ⟨157162563108253734248118853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209550084144338312330825137 157162563108253734248118853)
      ·
        refine ⟨29467980582797575171522285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157162563108253734248118853 29467980582797575171522285)
        ·
          refine ⟨11050492718549090689320857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29467980582797575171522285 11050492718549090689320857)
          ·
            refine ⟨8287869538911818016990643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11050492718549090689320857 8287869538911818016990643)
            ·
              refine ⟨12431804308367727025485965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8287869538911818016990643 12431804308367727025485965)
              ·
                refine ⟨4661926615637897634557237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12431804308367727025485965 4661926615637897634557237)
                ·
                  refine ⟨437055620216052903239741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4661926615637897634557237 437055620216052903239741)
                  ·
                    rfl

theorem cell23_7660465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 5].length) (baseStart_7660465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660465 prefixEnd_7660465 := by exact prefixLift 7660465
  have htrace : WordTrace (prefixWord ++ tailWord_7660465) baseStart_7660465 baseEnd_7660465 := by
    simpa [prefixWord, tailWord_7660465, baseEnd_7660465] using wordTrace_append hprefix tailTrace_7660465
  have hstable : (prefixWord ++ tailWord_7660465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660465).length < 2 ^ (prefixWord ++ tailWord_7660465).sum := by decide
  have hdescent : baseEnd_7660465 < baseStart_7660465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660524 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 8]
def baseStart_7660524 : Nat := 118140960795 + 7660524 * 2 ^ 59
def prefixEnd_7660524 : Nat := 4983230072969 + 3 ^ 40 * 7660524 * 2
def baseEnd_7660524 : Nat := 3933530877303091398319897

theorem tailTrace_7660524 : CollatzResearch.WordTrace tailWord_7660524 prefixEnd_7660524 3933530877303091398319897 := by
  unfold tailWord_7660524
  simp only [CollatzResearch.WordTrace]
  refine ⟨139701132049618668092082313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186268176066158224122776417 139701132049618668092082313)
  ·
    refine ⟨104775849037214001069061735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139701132049618668092082313 104775849037214001069061735)
    ·
      refine ⟨157163773555821001603592603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104775849037214001069061735 157163773555821001603592603)
      ·
        refine ⟨235745660333731502405388905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157163773555821001603592603 235745660333731502405388905)
        ·
          refine ⟨176809245250298626804041679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235745660333731502405388905 176809245250298626804041679)
          ·
            refine ⟨265213867875447940206062519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176809245250298626804041679 265213867875447940206062519)
            ·
              refine ⟨397820801813171910309093779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265213867875447940206062519 397820801813171910309093779)
              ·
                refine ⟨596731202719757865463640669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397820801813171910309093779 596731202719757865463640669)
                ·
                  refine ⟨223774201019909199548865251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596731202719757865463640669 223774201019909199548865251)
                  ·
                    refine ⟨335661301529863799323297877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 223774201019909199548865251 335661301529863799323297877)
                    ·
                      refine ⟨3933530877303091398319897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 335661301529863799323297877 3933530877303091398319897)
                      ·
                        rfl

theorem cell23_7660524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_7660524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660524 prefixEnd_7660524 := by exact prefixLift 7660524
  have htrace : WordTrace (prefixWord ++ tailWord_7660524) baseStart_7660524 baseEnd_7660524 := by
    simpa [prefixWord, tailWord_7660524, baseEnd_7660524] using wordTrace_append hprefix tailTrace_7660524
  have hstable : (prefixWord ++ tailWord_7660524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660524).length < 2 ^ (prefixWord ++ tailWord_7660524).sum := by decide
  have hdescent : baseEnd_7660524 < baseStart_7660524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660551 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 5, 5]
def baseStart_7660551 : Nat := 118140960795 + 7660551 * 2 ^ 59
def prefixEnd_7660551 : Nat := 4983230072969 + 3 ^ 40 * 7660551 * 2
def baseEnd_7660551 : Nat := 1311181580426920930894091

theorem tailTrace_7660551 : CollatzResearch.WordTrace tailWord_7660551 prefixEnd_7660551 1311181580426920930894091 := by
  unfold tailWord_7660551
  simp only [CollatzResearch.WordTrace]
  refine ⟨279403248870139519795397507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186268832580093013196931671 279403248870139519795397507)
  ·
    refine ⟨419104873305209279693096261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279403248870139519795397507 419104873305209279693096261)
    ·
      refine ⟨78582163744726739942455549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 419104873305209279693096261 78582163744726739942455549)
      ·
        refine ⟨29468311404272527478420831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78582163744726739942455549 29468311404272527478420831)
        ·
          refine ⟨44202467106408791217631247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29468311404272527478420831 44202467106408791217631247)
          ·
            refine ⟨66303700659613186826446871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44202467106408791217631247 66303700659613186826446871)
            ·
              refine ⟨99455550989419780239670307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66303700659613186826446871 99455550989419780239670307)
              ·
                refine ⟨149183326484129670359505461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99455550989419780239670307 149183326484129670359505461)
                ·
                  refine ⟨13985936857887156596203637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149183326484129670359505461 13985936857887156596203637)
                  ·
                    refine ⟨1311181580426920930894091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13985936857887156596203637 1311181580426920930894091)
                    ·
                      rfl

theorem cell23_7660551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_7660551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660551 prefixEnd_7660551 := by exact prefixLift 7660551
  have htrace : WordTrace (prefixWord ++ tailWord_7660551) baseStart_7660551 baseEnd_7660551 := by
    simpa [prefixWord, tailWord_7660551, baseEnd_7660551] using wordTrace_append hprefix tailTrace_7660551
  have hstable : (prefixWord ++ tailWord_7660551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660551).length < 2 ^ (prefixWord ++ tailWord_7660551).sum := by decide
  have hdescent : baseEnd_7660551 < baseStart_7660551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660565 : List Nat := [1, 3, 2, 1, 4, 2, 1, 2, 3, 1, 3]
def baseStart_7660565 : Nat := 118140960795 + 7660565 * 2 ^ 59
def prefixEnd_7660565 : Nat := 4983230072969 + 3 ^ 40 * 7660565 * 2
def baseEnd_7660565 : Nat := 3933551930009925737907209

theorem tailTrace_7660565 : CollatzResearch.WordTrace tailWord_7660565 prefixEnd_7660565 3933551930009925737907209 := by
  unfold tailWord_7660565
  simp only [CollatzResearch.WordTrace]
  refine ⟨279403759492088800186407149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186269172994725866790938099 279403759492088800186407149)
  ·
    refine ⟨104776409809533300069902681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279403759492088800186407149 104776409809533300069902681)
    ·
      refine ⟨78582307357149975052427011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104776409809533300069902681 78582307357149975052427011)
      ·
        refine ⟨117873461035724962578640517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78582307357149975052427011 117873461035724962578640517)
        ·
          refine ⟨22101273944198430483495097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117873461035724962578640517 22101273944198430483495097)
          ·
            refine ⟨16575955458148822862621323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22101273944198430483495097 16575955458148822862621323)
            ·
              refine ⟨24863933187223234293931985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16575955458148822862621323 24863933187223234293931985)
              ·
                refine ⟨18647949890417425720448989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24863933187223234293931985 18647949890417425720448989)
                ·
                  refine ⟨6992981208906534645168371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18647949890417425720448989 6992981208906534645168371)
                  ·
                    refine ⟨10489471813359801967752557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6992981208906534645168371 10489471813359801967752557)
                    ·
                      refine ⟨3933551930009925737907209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10489471813359801967752557 3933551930009925737907209)
                      ·
                        rfl

theorem cell23_7660565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_7660565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660565 prefixEnd_7660565 := by exact prefixLift 7660565
  have htrace : WordTrace (prefixWord ++ tailWord_7660565) baseStart_7660565 baseEnd_7660565 := by
    simpa [prefixWord, tailWord_7660565, baseEnd_7660565] using wordTrace_append hprefix tailTrace_7660565
  have hstable : (prefixWord ++ tailWord_7660565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660565).length < 2 ^ (prefixWord ++ tailWord_7660565).sum := by decide
  have hdescent : baseEnd_7660565 < baseStart_7660565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660575 : List Nat := [1, 1, 2, 4, 1, 3, 3, 1, 2, 3, 2]
def baseStart_7660575 : Nat := 118140960795 + 7660575 * 2 ^ 59
def prefixEnd_7660575 : Nat := 4983230072969 + 3 ^ 40 * 7660575 * 2
def baseEnd_7660575 : Nat := 3933557064816470698782163

theorem tailTrace_7660575 : CollatzResearch.WordTrace tailWord_7660575 prefixEnd_7660575 3933557064816470698782163 := by
  unfold tailWord_7660575
  simp only [CollatzResearch.WordTrace]
  refine ⟨279404124222052571894271179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186269416148035047929514119 279404124222052571894271179)
  ·
    refine ⟨419106186333078857841406769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279404124222052571894271179 419106186333078857841406769)
    ·
      refine ⟨314329639749809143381055077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419106186333078857841406769 314329639749809143381055077)
      ·
        refine ⟨58936807453089214383947827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314329639749809143381055077 58936807453089214383947827)
        ·
          refine ⟨88405211179633821575921741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58936807453089214383947827 88405211179633821575921741)
          ·
            refine ⟨33151954192362683090970653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88405211179633821575921741 33151954192362683090970653)
            ·
              refine ⟨12431982822136006159113995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33151954192362683090970653 12431982822136006159113995)
              ·
                refine ⟨18647974233204009238670993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12431982822136006159113995 18647974233204009238670993)
                ·
                  refine ⟨13985980674903006929003245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18647974233204009238670993 13985980674903006929003245)
                  ·
                    refine ⟨5244742753088627598376217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13985980674903006929003245 5244742753088627598376217)
                    ·
                      refine ⟨3933557064816470698782163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5244742753088627598376217 3933557064816470698782163)
                      ·
                        rfl

theorem cell23_7660575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_7660575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660575 prefixEnd_7660575 := by exact prefixLift 7660575
  have htrace : WordTrace (prefixWord ++ tailWord_7660575) baseStart_7660575 baseEnd_7660575 := by
    simpa [prefixWord, tailWord_7660575, baseEnd_7660575] using wordTrace_append hprefix tailTrace_7660575
  have hstable : (prefixWord ++ tailWord_7660575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660575).length < 2 ^ (prefixWord ++ tailWord_7660575).sum := by decide
  have hdescent : baseEnd_7660575 < baseStart_7660575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660581 : List Nat := [1, 3, 1, 2, 2, 2, 1, 4, 1, 6]
def baseStart_7660581 : Nat := 118140960795 + 7660581 * 2 ^ 59
def prefixEnd_7660581 : Nat := 4983230072969 + 3 ^ 40 * 7660581 * 2
def baseEnd_7660581 : Nat := 1311186715233465891769045

theorem tailTrace_7660581 : CollatzResearch.WordTrace tailWord_7660581 prefixEnd_7660581 1311186715233465891769045 := by
  unfold tailWord_7660581
  simp only [CollatzResearch.WordTrace]
  refine ⟨279404343060030834918989597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186269562040020556612659731 279404343060030834918989597)
  ·
    refine ⟨104776628647511563094621099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279404343060030834918989597 104776628647511563094621099)
    ·
      refine ⟨157164942971267344641931649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104776628647511563094621099 157164942971267344641931649)
      ·
        refine ⟨117873707228450508481448737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157164942971267344641931649 117873707228450508481448737)
        ·
          refine ⟨88405280421337881361086553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117873707228450508481448737 88405280421337881361086553)
          ·
            refine ⟨66303960316003411020814915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88405280421337881361086553 66303960316003411020814915)
            ·
              refine ⟨99455940474005116531222373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66303960316003411020814915 99455940474005116531222373)
              ·
                refine ⟨18647988838875959349604195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99455940474005116531222373 18647988838875959349604195)
                ·
                  refine ⟨27971983258313939024406293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18647988838875959349604195 27971983258313939024406293)
                  ·
                    refine ⟨1311186715233465891769045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27971983258313939024406293 1311186715233465891769045)
                    ·
                      rfl

theorem cell23_7660581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_7660581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660581 prefixEnd_7660581 := by exact prefixLift 7660581
  have htrace : WordTrace (prefixWord ++ tailWord_7660581) baseStart_7660581 baseEnd_7660581 := by
    simpa [prefixWord, tailWord_7660581, baseEnd_7660581] using wordTrace_append hprefix tailTrace_7660581
  have hstable : (prefixWord ++ tailWord_7660581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660581).length < 2 ^ (prefixWord ++ tailWord_7660581).sum := by decide
  have hdescent : baseEnd_7660581 < baseStart_7660581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660588 : List Nat := [2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 4]
def baseStart_7660588 : Nat := 118140960795 + 7660588 * 2 ^ 59
def prefixEnd_7660588 : Nat := 4983230072969 + 3 ^ 40 * 7660588 * 2
def baseEnd_7660588 : Nat := 3933563740064979147919603

theorem tailTrace_7660588 : CollatzResearch.WordTrace tailWord_7660588 prefixEnd_7660588 3933563740064979147919603 := by
  unfold tailWord_7660588
  simp only [CollatzResearch.WordTrace]
  refine ⟨139702299185502737557247209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186269732247336983409662945 139702299185502737557247209)
  ·
    refine ⟨104776724389127053167935407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139702299185502737557247209 104776724389127053167935407)
    ·
      refine ⟨157165086583690579751903111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104776724389127053167935407 157165086583690579751903111)
      ·
        refine ⟨235747629875535869627854667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157165086583690579751903111 235747629875535869627854667)
        ·
          refine ⟨353621444813303804441782001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235747629875535869627854667 353621444813303804441782001)
          ·
            refine ⟨265216083609977853331336501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353621444813303804441782001 265216083609977853331336501)
            ·
              refine ⟨24864007838435423749812797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 265216083609977853331336501 24864007838435423749812797)
              ·
                refine ⟨9324002939413283906179799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24864007838435423749812797 9324002939413283906179799)
                ·
                  refine ⟨13986004409119925859269699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9324002939413283906179799 13986004409119925859269699)
                  ·
                    refine ⟨20979006613679888788904549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13986004409119925859269699 20979006613679888788904549)
                    ·
                      refine ⟨3933563740064979147919603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20979006613679888788904549 3933563740064979147919603)
                      ·
                        rfl

theorem cell23_7660588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 4].length) (baseStart_7660588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660588 prefixEnd_7660588 := by exact prefixLift 7660588
  have htrace : WordTrace (prefixWord ++ tailWord_7660588) baseStart_7660588 baseEnd_7660588 := by
    simpa [prefixWord, tailWord_7660588, baseEnd_7660588] using wordTrace_append hprefix tailTrace_7660588
  have hstable : (prefixWord ++ tailWord_7660588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660588).length < 2 ^ (prefixWord ++ tailWord_7660588).sum := by decide
  have hdescent : baseEnd_7660588 < baseStart_7660588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660618 : List Nat := [3, 1, 2, 1, 1, 2, 5, 1, 1, 2, 4]
def baseStart_7660618 : Nat := 118140960795 + 7660618 * 2 ^ 59
def prefixEnd_7660618 : Nat := 4983230072969 + 3 ^ 40 * 7660618 * 2
def baseEnd_7660618 : Nat := 3933579144484614030544465

theorem tailTrace_7660618 : CollatzResearch.WordTrace tailWord_7660618 prefixEnd_7660618 3933579144484614030544465 := by
  unfold tailWord_7660618
  simp only [CollatzResearch.WordTrace]
  refine ⟨69851423140224197559521627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186270461707264526825391005 69851423140224197559521627)
  ·
    refine ⟨104777134710336296339282441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69851423140224197559521627 104777134710336296339282441)
    ·
      refine ⟨78582851032752222254461831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104777134710336296339282441 78582851032752222254461831)
      ·
        refine ⟨117874276549128333381692747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78582851032752222254461831 117874276549128333381692747)
        ·
          refine ⟨176811414823692500072539121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117874276549128333381692747 176811414823692500072539121)
          ·
            refine ⟨132608561117769375054404341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176811414823692500072539121 132608561117769375054404341)
            ·
              refine ⟨12432052604790878911350407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132608561117769375054404341 12432052604790878911350407)
              ·
                refine ⟨18648078907186318367025611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12432052604790878911350407 18648078907186318367025611)
                ·
                  refine ⟨27972118360779477550538417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18648078907186318367025611 27972118360779477550538417)
                  ·
                    refine ⟨20979088770584608162903813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27972118360779477550538417 20979088770584608162903813)
                    ·
                      refine ⟨3933579144484614030544465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20979088770584608162903813 3933579144484614030544465)
                      ·
                        rfl

theorem cell23_7660618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_7660618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660618 prefixEnd_7660618 := by exact prefixLift 7660618
  have htrace : WordTrace (prefixWord ++ tailWord_7660618) baseStart_7660618 baseEnd_7660618 := by
    simpa [prefixWord, tailWord_7660618, baseEnd_7660618] using wordTrace_append hprefix tailTrace_7660618
  have hstable : (prefixWord ++ tailWord_7660618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660618).length < 2 ^ (prefixWord ++ tailWord_7660618).sum := by decide
  have hdescent : baseEnd_7660618 < baseStart_7660618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660628 : List Nat := [2, 4, 1, 1, 1, 1, 6, 7]
def baseStart_7660628 : Nat := 118140960795 + 7660628 * 2 ^ 59
def prefixEnd_7660628 : Nat := 4983230072969 + 3 ^ 40 * 7660628 * 2
def baseEnd_7660628 : Nat := 145688306640413295978497

theorem tailTrace_7660628 : CollatzResearch.WordTrace tailWord_7660628 prefixEnd_7660628 145688306640413295978497 := by
  unfold tailWord_7660628
  simp only [CollatzResearch.WordTrace]
  refine ⟨139703028645430280972975269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186270704860573707963967025 139703028645430280972975269)
  ·
    refine ⟨26194317871018177682432863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139703028645430280972975269 26194317871018177682432863)
    ·
      refine ⟨39291476806527266523649295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26194317871018177682432863 39291476806527266523649295)
      ·
        refine ⟨58937215209790899785473943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39291476806527266523649295 58937215209790899785473943)
        ·
          refine ⟨88405822814686349678210915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58937215209790899785473943 88405822814686349678210915)
          ·
            refine ⟨132608734222029524517316373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88405822814686349678210915 132608734222029524517316373)
            ·
              refine ⟨6216034416657633961749205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132608734222029524517316373 6216034416657633961749205)
              ·
                refine ⟨145688306640413295978497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6216034416657633961749205 145688306640413295978497)
                ·
                  rfl

theorem cell23_7660628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 7].length) (baseStart_7660628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660628 prefixEnd_7660628 := by exact prefixLift 7660628
  have htrace : WordTrace (prefixWord ++ tailWord_7660628) baseStart_7660628 baseEnd_7660628 := by
    simpa [prefixWord, tailWord_7660628, baseEnd_7660628] using wordTrace_append hprefix tailTrace_7660628
  have hstable : (prefixWord ++ tailWord_7660628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660628).length < 2 ^ (prefixWord ++ tailWord_7660628).sum := by decide
  have hdescent : baseEnd_7660628 < baseStart_7660628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660642 : List Nat := [3, 3, 2, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_7660642 : Nat := 118140960795 + 7660642 * 2 ^ 59
def prefixEnd_7660642 : Nat := 4983230072969 + 3 ^ 40 * 7660642 * 2
def baseEnd_7660642 : Nat := 3933591468020321936644355

theorem tailTrace_7660642 : CollatzResearch.WordTrace tailWord_7660642 prefixEnd_7660642 3933591468020321936644355 := by
  unfold tailWord_7660642
  simp only [CollatzResearch.WordTrace]
  refine ⟨69851641978202460584240045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186271045275206561557973453 69851641978202460584240045)
  ·
    refine ⟨26194365741825922719090017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69851641978202460584240045 26194365741825922719090017)
    ·
      refine ⟨19645774306369442039317513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26194365741825922719090017 19645774306369442039317513)
      ·
        refine ⟨14734330729777081529488135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19645774306369442039317513 14734330729777081529488135)
        ·
          refine ⟨22101496094665622294232203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14734330729777081529488135 22101496094665622294232203)
          ·
            refine ⟨33152244141998433441348305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22101496094665622294232203 33152244141998433441348305)
            ·
              refine ⟨24864183106498825081011229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33152244141998433441348305 24864183106498825081011229)
              ·
                refine ⟨9324068664937059405379211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24864183106498825081011229 9324068664937059405379211)
                ·
                  refine ⟨13986102997405589108068817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9324068664937059405379211 13986102997405589108068817)
                  ·
                    refine ⟨10489577248054191831051613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13986102997405589108068817 10489577248054191831051613)
                    ·
                      refine ⟨3933591468020321936644355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10489577248054191831051613 3933591468020321936644355)
                      ·
                        rfl

theorem cell23_7660642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_7660642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660642 prefixEnd_7660642 := by exact prefixLift 7660642
  have htrace : WordTrace (prefixWord ++ tailWord_7660642) baseStart_7660642 baseEnd_7660642 := by
    simpa [prefixWord, tailWord_7660642, baseEnd_7660642] using wordTrace_append hprefix tailTrace_7660642
  have hstable : (prefixWord ++ tailWord_7660642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660642).length < 2 ^ (prefixWord ++ tailWord_7660642).sum := by decide
  have hdescent : baseEnd_7660642 < baseStart_7660642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660655 : List Nat := [1, 1, 2, 1, 3, 3, 2, 4, 2, 1, 3]
def baseStart_7660655 : Nat := 118140960795 + 7660655 * 2 ^ 59
def prefixEnd_7660655 : Nat := 4983230072969 + 3 ^ 40 * 7660655 * 2
def baseEnd_7660655 : Nat := 3933598143268830385781795

theorem tailTrace_7660655 : CollatzResearch.WordTrace tailWord_7660655 prefixEnd_7660655 3933598143268830385781795 := by
  unfold tailWord_7660655
  simp only [CollatzResearch.WordTrace]
  refine ⟨279407042061762745557183419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186271361374508497038122279 279407042061762745557183419)
  ·
    refine ⟨419110563092644118335775129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279407042061762745557183419 419110563092644118335775129)
    ·
      refine ⟨314332922319483088751831347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419110563092644118335775129 314332922319483088751831347)
      ·
        refine ⟨471499383479224633127747021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314332922319483088751831347 471499383479224633127747021)
        ·
          refine ⟨176812268804709237422905133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 471499383479224633127747021 176812268804709237422905133)
          ·
            refine ⟨66304600801765964033589425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176812268804709237422905133 66304600801765964033589425)
            ·
              refine ⟨49728450601324473025192069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66304600801765964033589425 49728450601324473025192069)
              ·
                refine ⟨9324084487748338692223513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49728450601324473025192069 9324084487748338692223513)
                ·
                  refine ⟨6993063365811254019167635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9324084487748338692223513 6993063365811254019167635)
                  ·
                    refine ⟨10489595048716881028751453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6993063365811254019167635 10489595048716881028751453)
                    ·
                      refine ⟨3933598143268830385781795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10489595048716881028751453 3933598143268830385781795)
                      ·
                        rfl

theorem cell23_7660655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 1, 3].length) (baseStart_7660655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660655 prefixEnd_7660655 := by exact prefixLift 7660655
  have htrace : WordTrace (prefixWord ++ tailWord_7660655) baseStart_7660655 baseEnd_7660655 := by
    simpa [prefixWord, tailWord_7660655, baseEnd_7660655] using wordTrace_append hprefix tailTrace_7660655
  have hstable : (prefixWord ++ tailWord_7660655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660655).length < 2 ^ (prefixWord ++ tailWord_7660655).sum := by decide
  have hdescent : baseEnd_7660655 < baseStart_7660655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660672 : List Nat := [2, 1, 1, 2, 1, 3, 6, 1, 2, 1, 3]
def baseStart_7660672 : Nat := 118140960795 + 7660672 * 2 ^ 59
def prefixEnd_7660672 : Nat := 4983230072969 + 3 ^ 40 * 7660672 * 2
def baseEnd_7660672 : Nat := 3933606872439956819269217

theorem tailTrace_7660672 : CollatzResearch.WordTrace tailWord_7660672 prefixEnd_7660672 3933606872439956819269217 := by
  unfold tailWord_7660672
  simp only [CollatzResearch.WordTrace]
  refine ⟨139703831051350578730276135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186271774735134104973701513 139703831051350578730276135)
  ·
    refine ⟨209555746577025868095414203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139703831051350578730276135 209555746577025868095414203)
    ·
      refine ⟨314333619865538802143121305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209555746577025868095414203 314333619865538802143121305)
      ·
        refine ⟨235750214899154101607340979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314333619865538802143121305 235750214899154101607340979)
        ·
          refine ⟨353625322348731152411011469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235750214899154101607340979 353625322348731152411011469)
          ·
            refine ⟨132609495880774182154129301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353625322348731152411011469 132609495880774182154129301)
            ·
              refine ⟨6216070119411289788474811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132609495880774182154129301 6216070119411289788474811)
              ·
                refine ⟨9324105179116934682712217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6216070119411289788474811 9324105179116934682712217)
                ·
                  refine ⟨6993078884337701012034163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9324105179116934682712217 6993078884337701012034163)
                  ·
                    refine ⟨10489618326506551518051245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6993078884337701012034163 10489618326506551518051245)
                    ·
                      refine ⟨3933606872439956819269217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10489618326506551518051245 3933606872439956819269217)
                      ·
                        rfl

theorem cell23_7660672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 2, 1, 3].length) (baseStart_7660672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660672 prefixEnd_7660672 := by exact prefixLift 7660672
  have htrace : WordTrace (prefixWord ++ tailWord_7660672) baseStart_7660672 baseEnd_7660672 := by
    simpa [prefixWord, tailWord_7660672, baseEnd_7660672] using wordTrace_append hprefix tailTrace_7660672
  have hstable : (prefixWord ++ tailWord_7660672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660672).length < 2 ^ (prefixWord ++ tailWord_7660672).sum := by decide
  have hdescent : baseEnd_7660672 < baseStart_7660672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660695 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 3, 4, 2]
def baseStart_7660695 : Nat := 118140960795 + 7660695 * 2 ^ 59
def prefixEnd_7660695 : Nat := 4983230072969 + 3 ^ 40 * 7660695 * 2
def baseEnd_7660695 : Nat := 3933618682495010229281611

theorem tailTrace_7660695 : CollatzResearch.WordTrace tailWord_7660695 prefixEnd_7660695 3933618682495010229281611 := by
  unfold tailWord_7660695
  simp only [CollatzResearch.WordTrace]
  refine ⟨279408500981617832388639539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186272333987745221592426359 279408500981617832388639539)
  ·
    refine ⟨419112751472426748582959309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279408500981617832388639539 419112751472426748582959309)
    ·
      refine ⟨157167281802160030718609741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419112751472426748582959309 157167281802160030718609741)
      ·
        refine ⟨58937730675810011519478653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157167281802160030718609741 58937730675810011519478653)
        ·
          refine ⟨22101649003428754319804495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58937730675810011519478653 22101649003428754319804495)
          ·
            refine ⟨33152473505143131479706743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22101649003428754319804495 33152473505143131479706743)
            ·
              refine ⟨49728710257714697219560115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33152473505143131479706743 49728710257714697219560115)
              ·
                refine ⟨74593065386572045829340173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49728710257714697219560115 74593065386572045829340173)
                ·
                  refine ⟨27972399519964517186002565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74593065386572045829340173 27972399519964517186002565)
                  ·
                    refine ⟨5244824909993346972375481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27972399519964517186002565 5244824909993346972375481)
                    ·
                      refine ⟨3933618682495010229281611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5244824909993346972375481 3933618682495010229281611)
                      ·
                        rfl

theorem cell23_7660695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_7660695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660695 prefixEnd_7660695 := by exact prefixLift 7660695
  have htrace : WordTrace (prefixWord ++ tailWord_7660695) baseStart_7660695 baseEnd_7660695 := by
    simpa [prefixWord, tailWord_7660695, baseEnd_7660695] using wordTrace_append hprefix tailTrace_7660695
  have hstable : (prefixWord ++ tailWord_7660695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660695).length < 2 ^ (prefixWord ++ tailWord_7660695).sum := by decide
  have hdescent : baseEnd_7660695 < baseStart_7660695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660805 : List Nat := [1, 3, 1, 1, 2, 1, 4, 3, 2, 2, 3]
def baseStart_7660805 : Nat := 118140960795 + 7660805 * 2 ^ 59
def prefixEnd_7660805 : Nat := 4983230072969 + 3 ^ 40 * 7660805 * 2
def baseEnd_7660805 : Nat := 3933675165367004798906105

theorem tailTrace_7660805 : CollatzResearch.WordTrace tailWord_7660805 prefixEnd_7660805 3933675165367004798906105 := by
  unfold tailWord_7660805
  simp only [CollatzResearch.WordTrace]
  refine ⟨279412513011219321175143869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186275008674146214116762579 279412513011219321175143869)
  ·
    refine ⟨104779692379207245440678951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279412513011219321175143869 104779692379207245440678951)
    ·
      refine ⟨157169538568810868161018427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104779692379207245440678951 157169538568810868161018427)
      ·
        refine ⟨235754307853216302241527641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157169538568810868161018427 235754307853216302241527641)
        ·
          refine ⟨176815730889912226681145731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235754307853216302241527641 176815730889912226681145731)
          ·
            refine ⟨265223596334868340021718597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176815730889912226681145731 265223596334868340021718597)
            ·
              refine ⟨49729424312787813754072237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265223596334868340021718597 49729424312787813754072237)
              ·
                refine ⟨18648534117295430157777089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49729424312787813754072237 18648534117295430157777089)
                ·
                  refine ⟨13986400587971572618332817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18648534117295430157777089 13986400587971572618332817)
                  ·
                    refine ⟨10489800440978679463749613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13986400587971572618332817 10489800440978679463749613)
                    ·
                      refine ⟨3933675165367004798906105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10489800440978679463749613 3933675165367004798906105)
                      ·
                        rfl

theorem cell23_7660805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_7660805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660805 prefixEnd_7660805 := by exact prefixLift 7660805
  have htrace : WordTrace (prefixWord ++ tailWord_7660805) baseStart_7660805 baseEnd_7660805 := by
    simpa [prefixWord, tailWord_7660805, baseEnd_7660805] using wordTrace_append hprefix tailTrace_7660805
  have hstable : (prefixWord ++ tailWord_7660805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660805).length < 2 ^ (prefixWord ++ tailWord_7660805).sum := by decide
  have hdescent : baseEnd_7660805 < baseStart_7660805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660828 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_7660828 : Nat := 118140960795 + 7660828 * 2 ^ 59
def prefixEnd_7660828 : Nat := 4983230072969 + 3 ^ 40 * 7660828 * 2
def baseEnd_7660828 : Nat := 3933686975422058208918499

theorem tailTrace_7660828 : CollatzResearch.WordTrace tailWord_7660828 prefixEnd_7660828 3933686975422058208918499 := by
  unfold tailWord_7660828
  simp only [CollatzResearch.WordTrace]
  refine ⟨139706675945067998051615569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186275567926757330735487425 139706675945067998051615569)
  ·
    refine ⟨104780006958800998538711677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139706675945067998051615569 104780006958800998538711677)
    ·
      refine ⟨39292502609550374452016879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104780006958800998538711677 39292502609550374452016879)
      ·
        refine ⟨58938753914325561678025319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39292502609550374452016879 58938753914325561678025319)
        ·
          refine ⟨88408130871488342517037979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58938753914325561678025319 88408130871488342517037979)
          ·
            refine ⟨132612196307232513775556969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88408130871488342517037979 132612196307232513775556969)
            ·
              refine ⟨99459147230424385331667727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132612196307232513775556969 99459147230424385331667727)
              ·
                refine ⟨149188720845636577997501591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99459147230424385331667727 149188720845636577997501591)
                ·
                  refine ⟨223783081268454866996252387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149188720845636577997501591 223783081268454866996252387)
                  ·
                    refine ⟨335674621902682300494378581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 223783081268454866996252387 335674621902682300494378581)
                    ·
                      refine ⟨3933686975422058208918499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 335674621902682300494378581 3933686975422058208918499)
                      ·
                        rfl

theorem cell23_7660828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_7660828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660828 prefixEnd_7660828 := by exact prefixLift 7660828
  have htrace : WordTrace (prefixWord ++ tailWord_7660828) baseStart_7660828 baseEnd_7660828 := by
    simpa [prefixWord, tailWord_7660828, baseEnd_7660828] using wordTrace_append hprefix tailTrace_7660828
  have hstable : (prefixWord ++ tailWord_7660828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660828).length < 2 ^ (prefixWord ++ tailWord_7660828).sum := by decide
  have hdescent : baseEnd_7660828 < baseStart_7660828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660829 : List Nat := [1, 4, 2, 3, 1, 3, 1, 1, 3, 4]
def baseStart_7660829 : Nat := 118140960795 + 7660829 * 2 ^ 59
def prefixEnd_7660829 : Nat := 4983230072969 + 3 ^ 40 * 7660829 * 2
def baseEnd_7660829 : Nat := 1311229162967570901668665

theorem tailTrace_7660829 : CollatzResearch.WordTrace tailWord_7660829 prefixEnd_7660829 1311229162967570901668665 := by
  unfold tailWord_7660829
  simp only [CollatzResearch.WordTrace]
  refine ⟨279413388363132373274017541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186275592242088248849345027 279413388363132373274017541)
  ·
    refine ⟨52390010318087319988878289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279413388363132373274017541 52390010318087319988878289)
    ·
      refine ⟨39292507738565489991658717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52390010318087319988878289 39292507738565489991658717)
      ·
        refine ⟨14734690401962058746872019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39292507738565489991658717 14734690401962058746872019)
        ·
          refine ⟨22102035602943088120308029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14734690401962058746872019 22102035602943088120308029)
          ·
            refine ⟨8288263351103658045115511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22102035602943088120308029 8288263351103658045115511)
            ·
              refine ⟨12432395026655487067673267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8288263351103658045115511 12432395026655487067673267)
              ·
                refine ⟨18648592539983230601509901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12432395026655487067673267 18648592539983230601509901)
                ·
                  refine ⟨6993222202493711475566213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18648592539983230601509901 6993222202493711475566213)
                  ·
                    refine ⟨1311229162967570901668665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6993222202493711475566213 1311229162967570901668665)
                    ·
                      rfl

theorem cell23_7660829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_7660829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660829 prefixEnd_7660829 := by exact prefixLift 7660829
  have htrace : WordTrace (prefixWord ++ tailWord_7660829) baseStart_7660829 baseEnd_7660829 := by
    simpa [prefixWord, tailWord_7660829, baseEnd_7660829] using wordTrace_append hprefix tailTrace_7660829
  have hstable : (prefixWord ++ tailWord_7660829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660829).length < 2 ^ (prefixWord ++ tailWord_7660829).sum := by decide
  have hdescent : baseEnd_7660829 < baseStart_7660829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660842 : List Nat := [3, 1, 4, 2, 1, 2, 1, 3, 6]
def baseStart_7660842 : Nat := 118140960795 + 7660842 * 2 ^ 59
def prefixEnd_7660842 : Nat := 4983230072969 + 3 ^ 40 * 7660842 * 2
def baseEnd_7660842 : Nat := 437077129350135683793715

theorem tailTrace_7660842 : CollatzResearch.WordTrace tailWord_7660842 prefixEnd_7660842 437077129350135683793715 := by
  unfold tailWord_7660842
  simp only [CollatzResearch.WordTrace]
  refine ⟨69853465628021319123560195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186275908341390184329493853 69853465628021319123560195)
  ·
    refine ⟨104780198442031978685340293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69853465628021319123560195 104780198442031978685340293)
    ·
      refine ⟨19646287207880996003501305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104780198442031978685340293 19646287207880996003501305)
      ·
        refine ⟨14734715405910747002625979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19646287207880996003501305 14734715405910747002625979)
        ·
          refine ⟨22102073108866120503938969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14734715405910747002625979 22102073108866120503938969)
          ·
            refine ⟨16576554831649590377954227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22102073108866120503938969 16576554831649590377954227)
            ·
              refine ⟨24864832247474385566931341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16576554831649590377954227 24864832247474385566931341)
              ·
                refine ⟨9324312092802894587599253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24864832247474385566931341 9324312092802894587599253)
                ·
                  refine ⟨437077129350135683793715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9324312092802894587599253 437077129350135683793715)
                  ·
                    rfl

theorem cell23_7660842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 6].length) (baseStart_7660842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660842 prefixEnd_7660842 := by exact prefixLift 7660842
  have htrace : WordTrace (prefixWord ++ tailWord_7660842) baseStart_7660842 baseEnd_7660842 := by
    simpa [prefixWord, tailWord_7660842, baseEnd_7660842] using wordTrace_append hprefix tailTrace_7660842
  have hstable : (prefixWord ++ tailWord_7660842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660842).length < 2 ^ (prefixWord ++ tailWord_7660842).sum := by decide
  have hdescent : baseEnd_7660842 < baseStart_7660842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660875 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 4, 6, 2]
def baseStart_7660875 : Nat := 118140960795 + 7660875 * 2 ^ 59
def prefixEnd_7660875 : Nat := 4983230072969 + 3 ^ 40 * 7660875 * 2
def baseEnd_7660875 : Nat := 3933711109012819525030783

theorem tailTrace_7660875 : CollatzResearch.WordTrace tailWord_7660875 prefixEnd_7660875 3933711109012819525030783 := by
  unfold tailWord_7660875
  simp only [CollatzResearch.WordTrace]
  refine ⟨279415066120965723130192079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186276710747310482086794719 279415066120965723130192079)
  ·
    refine ⟨419122599181448584695288119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279415066120965723130192079 419122599181448584695288119)
    ·
      refine ⟨628683898772172877042932179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419122599181448584695288119 628683898772172877042932179)
      ·
        refine ⟨943025848158259315564398269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628683898772172877042932179 943025848158259315564398269)
        ·
          refine ⟨353634693059347243336649351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 943025848158259315564398269 353634693059347243336649351)
          ·
            refine ⟨530452039589020865004974027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353634693059347243336649351 530452039589020865004974027)
            ·
              refine ⟨795678059383531297507461041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530452039589020865004974027 795678059383531297507461041)
              ·
                refine ⟨596758544537648473130595781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795678059383531297507461041 596758544537648473130595781)
                ·
                  refine ⟨111892227100809088711986709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 596758544537648473130595781 111892227100809088711986709)
                  ·
                    refine ⟨5244948145350426033374377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111892227100809088711986709 5244948145350426033374377)
                    ·
                      refine ⟨3933711109012819525030783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5244948145350426033374377 3933711109012819525030783)
                      ·
                        rfl

theorem cell23_7660875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 6, 2].length) (baseStart_7660875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660875 prefixEnd_7660875 := by exact prefixLift 7660875
  have htrace : WordTrace (prefixWord ++ tailWord_7660875) baseStart_7660875 baseEnd_7660875 := by
    simpa [prefixWord, tailWord_7660875, baseEnd_7660875] using wordTrace_append hprefix tailTrace_7660875
  have hstable : (prefixWord ++ tailWord_7660875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660875).length < 2 ^ (prefixWord ++ tailWord_7660875).sum := by decide
  have hdescent : baseEnd_7660875 < baseStart_7660875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660909 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 5, 2, 2]
def baseStart_7660909 : Nat := 118140960795 + 7660909 * 2 ^ 59
def prefixEnd_7660909 : Nat := 4983230072969 + 3 ^ 40 * 7660909 * 2
def baseEnd_7660909 : Nat := 3933728567355072392005627

theorem tailTrace_7660909 : CollatzResearch.WordTrace tailWord_7660909 prefixEnd_7660909 3933728567355072392005627 := by
  unfold tailWord_7660909
  simp only [CollatzResearch.WordTrace]
  refine ⟨279416306202842546936929781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186277537468561697957953187 279416306202842546936929781)
  ·
    refine ⟨26195278706516488775337167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279416306202842546936929781 26195278706516488775337167)
    ·
      refine ⟨39292918059774733163005751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26195278706516488775337167 39292918059774733163005751)
      ·
        refine ⟨58939377089662099744508627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39292918059774733163005751 58939377089662099744508627)
        ·
          refine ⟨88409065634493149616762941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58939377089662099744508627 88409065634493149616762941)
          ·
            refine ⟨33153399612934931106286103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88409065634493149616762941 33153399612934931106286103)
            ·
              refine ⟨49730099419402396659429155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33153399612934931106286103 49730099419402396659429155)
              ·
                refine ⟨74595149129103594989143733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49730099419402396659429155 74595149129103594989143733)
                ·
                  refine ⟨6993295230853462030232225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74595149129103594989143733 6993295230853462030232225)
                  ·
                    refine ⟨5244971423140096522674169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6993295230853462030232225 5244971423140096522674169)
                    ·
                      refine ⟨3933728567355072392005627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5244971423140096522674169 3933728567355072392005627)
                      ·
                        rfl

theorem cell23_7660909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_7660909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660909 prefixEnd_7660909 := by exact prefixLift 7660909
  have htrace : WordTrace (prefixWord ++ tailWord_7660909) baseStart_7660909 baseEnd_7660909 := by
    simpa [prefixWord, tailWord_7660909, baseEnd_7660909] using wordTrace_append hprefix tailTrace_7660909
  have hstable : (prefixWord ++ tailWord_7660909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660909).length < 2 ^ (prefixWord ++ tailWord_7660909).sum := by decide
  have hdescent : baseEnd_7660909 < baseStart_7660909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660912 : List Nat := [2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 3]
def baseStart_7660912 : Nat := 118140960795 + 7660912 * 2 ^ 59
def prefixEnd_7660912 : Nat := 4983230072969 + 3 ^ 40 * 7660912 * 2
def baseEnd_7660912 : Nat := 3933730107797035880268113

theorem tailTrace_7660912 : CollatzResearch.WordTrace tailWord_7660912 prefixEnd_7660912 3933730107797035880268113 := by
  unfold tailWord_7660912
  simp only [CollatzResearch.WordTrace]
  refine ⟨139708207810915839224644495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186277610414554452299525993 139708207810915839224644495)
  ·
    refine ⟨209562311716373758836966743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139708207810915839224644495 209562311716373758836966743)
    ·
      refine ⟨314343467574560638255450115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209562311716373758836966743 314343467574560638255450115)
      ·
        refine ⟨471515201361840957383175173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314343467574560638255450115 471515201361840957383175173)
        ·
          refine ⟨88409100255345179509345345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 471515201361840957383175173 88409100255345179509345345)
          ·
            refine ⟨66306825191508884632009009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88409100255345179509345345 66306825191508884632009009)
            ·
              refine ⟨49730118893631663474006757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66306825191508884632009009 49730118893631663474006757)
              ·
                refine ⟨9324397292555936901376267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49730118893631663474006757 9324397292555936901376267)
                ·
                  refine ⟨13986595938833905352064401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9324397292555936901376267 13986595938833905352064401)
                  ·
                    refine ⟨10489946954125429014048301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13986595938833905352064401 10489946954125429014048301)
                    ·
                      refine ⟨3933730107797035880268113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10489946954125429014048301 3933730107797035880268113)
                      ·
                        rfl

theorem cell23_7660912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 3].length) (baseStart_7660912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660912 prefixEnd_7660912 := by exact prefixLift 7660912
  have htrace : WordTrace (prefixWord ++ tailWord_7660912) baseStart_7660912 baseEnd_7660912 := by
    simpa [prefixWord, tailWord_7660912, baseEnd_7660912] using wordTrace_append hprefix tailTrace_7660912
  have hstable : (prefixWord ++ tailWord_7660912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660912).length < 2 ^ (prefixWord ++ tailWord_7660912).sum := by decide
  have hdescent : baseEnd_7660912 < baseStart_7660912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660956 : List Nat := [2, 2, 3, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_7660956 : Nat := 118140960795 + 7660956 * 2 ^ 59
def prefixEnd_7660956 : Nat := 4983230072969 + 3 ^ 40 * 7660956 * 2
def baseEnd_7660956 : Nat := 3933752700945833708117911

theorem tailTrace_7660956 : CollatzResearch.WordTrace tailWord_7660956 prefixEnd_7660956 3933752700945833708117911 := by
  unfold tailWord_7660956
  simp only [CollatzResearch.WordTrace]
  refine ⟨139709010216836136981945361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186278680289114849309260481 139709010216836136981945361)
  ·
    refine ⟨104781757662627102736459021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139709010216836136981945361 104781757662627102736459021)
    ·
      refine ⟨39293159123485163526172133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104781757662627102736459021 39293159123485163526172133)
      ·
        refine ⟨7367467335653468161157275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39293159123485163526172133 7367467335653468161157275)
        ·
          refine ⟨11051201003480202241735913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7367467335653468161157275 11051201003480202241735913)
          ·
            refine ⟨8288400752610151681301935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11051201003480202241735913 8288400752610151681301935)
            ·
              refine ⟨12432601128915227521952903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8288400752610151681301935 12432601128915227521952903)
              ·
                refine ⟨18648901693372841282929355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12432601128915227521952903 18648901693372841282929355)
                ·
                  refine ⟨27973352540059261924394033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18648901693372841282929355 27973352540059261924394033)
                  ·
                    refine ⟨20980014405044446443295525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27973352540059261924394033 20980014405044446443295525)
                    ·
                      refine ⟨3933752700945833708117911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20980014405044446443295525 3933752700945833708117911)
                      ·
                        rfl

theorem cell23_7660956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_7660956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660956 prefixEnd_7660956 := by exact prefixLift 7660956
  have htrace : WordTrace (prefixWord ++ tailWord_7660956) baseStart_7660956 baseEnd_7660956 := by
    simpa [prefixWord, tailWord_7660956, baseEnd_7660956] using wordTrace_append hprefix tailTrace_7660956
  have hstable : (prefixWord ++ tailWord_7660956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660956).length < 2 ^ (prefixWord ++ tailWord_7660956).sum := by decide
  have hdescent : baseEnd_7660956 < baseStart_7660956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660959 : List Nat := [1, 1, 2, 5, 1, 4, 1, 1, 1, 3, 3]
def baseStart_7660959 : Nat := 118140960795 + 7660959 * 2 ^ 59
def prefixEnd_7660959 : Nat := 4983230072969 + 3 ^ 40 * 7660959 * 2
def baseEnd_7660959 : Nat := 3933754241387797196380397

theorem tailTrace_7660959 : CollatzResearch.WordTrace tailWord_7660959 prefixEnd_7660959 3933754241387797196380397 := by
  unfold tailWord_7660959
  simp only [CollatzResearch.WordTrace]
  refine ⟨279418129852661405476249931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186278753235107603650833287 279418129852661405476249931)
  ·
    refine ⟨419127194778992108214374897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279418129852661405476249931 419127194778992108214374897)
    ·
      refine ⟨314345396084244081160781173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419127194778992108214374897 314345396084244081160781173)
      ·
        refine ⟨29469880882897882608823235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 314345396084244081160781173 29469880882897882608823235)
        ·
          refine ⟨44204821324346823913234853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29469880882897882608823235 44204821324346823913234853)
          ·
            refine ⟨8288403998315029483731535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44204821324346823913234853 8288403998315029483731535)
            ·
              refine ⟨12432605997472544225597303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8288403998315029483731535 12432605997472544225597303)
              ·
                refine ⟨18648908996208816338395955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12432605997472544225597303 18648908996208816338395955)
                ·
                  refine ⟨27973363494313224507593933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18648908996208816338395955 27973363494313224507593933)
                  ·
                    refine ⟨10490011310367459190347725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27973363494313224507593933 10490011310367459190347725)
                    ·
                      refine ⟨3933754241387797196380397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10490011310367459190347725 3933754241387797196380397)
                      ·
                        rfl

theorem cell23_7660959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_7660959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660959 prefixEnd_7660959 := by exact prefixLift 7660959
  have htrace : WordTrace (prefixWord ++ tailWord_7660959) baseStart_7660959 baseEnd_7660959 := by
    simpa [prefixWord, tailWord_7660959, baseEnd_7660959] using wordTrace_append hprefix tailTrace_7660959
  have hstable : (prefixWord ++ tailWord_7660959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660959).length < 2 ^ (prefixWord ++ tailWord_7660959).sum := by decide
  have hdescent : baseEnd_7660959 < baseStart_7660959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660994 : List Nat := [3, 5, 2, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_7660994 : Nat := 118140960795 + 7660994 * 2 ^ 59
def prefixEnd_7660994 : Nat := 4983230072969 + 3 ^ 40 * 7660994 * 2
def baseEnd_7660994 : Nat := 3933772213210704559442737

theorem tailTrace_7660994 : CollatzResearch.WordTrace tailWord_7660994 prefixEnd_7660994 3933772213210704559442737 := by
  unfold tailWord_7660994
  simp only [CollatzResearch.WordTrace]
  refine ⟨69854851601883651613443509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186279604271689737635849357 69854851601883651613443509)
  ·
    refine ⟨6548892337676592338760329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69854851601883651613443509 6548892337676592338760329)
    ·
      refine ⟨4911669253257444254070247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6548892337676592338760329 4911669253257444254070247)
      ·
        refine ⟨7367503879886166381105371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4911669253257444254070247 7367503879886166381105371)
        ·
          refine ⟨11051255819829249571658057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7367503879886166381105371 11051255819829249571658057)
          ·
            refine ⟨8288441864871937178743543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11051255819829249571658057 8288441864871937178743543)
            ·
              refine ⟨12432662797307905768115315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8288441864871937178743543 12432662797307905768115315)
              ·
                refine ⟨18648994195961858652172973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12432662797307905768115315 18648994195961858652172973)
                ·
                  refine ⟨6993372823485696994564865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18648994195961858652172973 6993372823485696994564865)
                  ·
                    refine ⟨5245029617614272745923649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6993372823485696994564865 5245029617614272745923649)
                    ·
                      refine ⟨3933772213210704559442737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245029617614272745923649 3933772213210704559442737)
                      ·
                        rfl

theorem cell23_7660994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_7660994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660994 prefixEnd_7660994 := by exact prefixLift 7660994
  have htrace : WordTrace (prefixWord ++ tailWord_7660994) baseStart_7660994 baseEnd_7660994 := by
    simpa [prefixWord, tailWord_7660994, baseEnd_7660994] using wordTrace_append hprefix tailTrace_7660994
  have hstable : (prefixWord ++ tailWord_7660994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660994).length < 2 ^ (prefixWord ++ tailWord_7660994).sum := by decide
  have hdescent : baseEnd_7660994 < baseStart_7660994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660995 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 4]
def baseStart_7660995 : Nat := 118140960795 + 7660995 * 2 ^ 59
def prefixEnd_7660995 : Nat := 4983230072969 + 3 ^ 40 * 7660995 * 2
def baseEnd_7660995 : Nat := 3933772726691359055530231

theorem tailTrace_7660995 : CollatzResearch.WordTrace tailWord_7660995 prefixEnd_7660995 3933772726691359055530231 := by
  unfold tailWord_7660995
  simp only [CollatzResearch.WordTrace]
  refine ⟨279419442880530983624560439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186279628587020655749706959 279419442880530983624560439)
  ·
    refine ⟨419129164320796475436840659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279419442880530983624560439 419129164320796475436840659)
    ·
      refine ⟨628693746481194713155260989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419129164320796475436840659 628693746481194713155260989)
      ·
        refine ⟨235760154930448017433222871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 628693746481194713155260989 235760154930448017433222871)
        ·
          refine ⟨353640232395672026149834307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235760154930448017433222871 353640232395672026149834307)
          ·
            refine ⟨530460348593508039224751461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353640232395672026149834307 530460348593508039224751461)
            ·
              refine ⟨99461315361282757354640899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 530460348593508039224751461 99461315361282757354640899)
              ·
                refine ⟨149191973041924136031961349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99461315361282757354640899 149191973041924136031961349)
                ·
                  refine ⟨27973494945360775505992753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149191973041924136031961349 27973494945360775505992753)
                  ·
                    refine ⟨20980121209020581629494565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27973494945360775505992753 20980121209020581629494565)
                    ·
                      refine ⟨3933772726691359055530231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20980121209020581629494565 3933772726691359055530231)
                      ·
                        rfl

theorem cell23_7660995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_7660995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660995 prefixEnd_7660995 := by exact prefixLift 7660995
  have htrace : WordTrace (prefixWord ++ tailWord_7660995) baseStart_7660995 baseEnd_7660995 := by
    simpa [prefixWord, tailWord_7660995, baseEnd_7660995] using wordTrace_append hprefix tailTrace_7660995
  have hstable : (prefixWord ++ tailWord_7660995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660995).length < 2 ^ (prefixWord ++ tailWord_7660995).sum := by decide
  have hdescent : baseEnd_7660995 < baseStart_7660995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7660999 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 4, 2, 2]
def baseStart_7660999 : Nat := 118140960795 + 7660999 * 2 ^ 59
def prefixEnd_7660999 : Nat := 4983230072969 + 3 ^ 40 * 7660999 * 2
def baseEnd_7660999 : Nat := 3933774780613977039880213

theorem tailTrace_7660999 : CollatzResearch.WordTrace tailWord_7660999 prefixEnd_7660999 3933774780613977039880213 := by
  unfold tailWord_7660999
  simp only [CollatzResearch.WordTrace]
  refine ⟨279419588772516492307706051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186279725848344328205137367 279419588772516492307706051)
  ·
    refine ⟨419129383158774738461559077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279419588772516492307706051 419129383158774738461559077)
    ·
      refine ⟨78586759342270263461542327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 419129383158774738461559077 78586759342270263461542327)
      ·
        refine ⟨117880139013405395192313491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78586759342270263461542327 117880139013405395192313491)
        ·
          refine ⟨176820208520108092788470237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117880139013405395192313491 176820208520108092788470237)
          ·
            refine ⟨66307578195040534795676339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176820208520108092788470237 66307578195040534795676339)
            ·
              refine ⟨99461367292560802193514509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66307578195040534795676339 99461367292560802193514509)
              ·
                refine ⟨37298012734710300822567941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99461367292560802193514509 37298012734710300822567941)
                ·
                  refine ⟨6993377387758181404231489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37298012734710300822567941 6993377387758181404231489)
                  ·
                    refine ⟨5245033040818636053173617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6993377387758181404231489 5245033040818636053173617)
                    ·
                      refine ⟨3933774780613977039880213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245033040818636053173617 3933774780613977039880213)
                      ·
                        rfl

theorem cell23_7660999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_7660999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7660999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7660999 prefixEnd_7660999 := by exact prefixLift 7660999
  have htrace : WordTrace (prefixWord ++ tailWord_7660999) baseStart_7660999 baseEnd_7660999 := by
    simpa [prefixWord, tailWord_7660999, baseEnd_7660999] using wordTrace_append hprefix tailTrace_7660999
  have hstable : (prefixWord ++ tailWord_7660999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7660999).length < 2 ^ (prefixWord ++ tailWord_7660999).sum := by decide
  have hdescent : baseEnd_7660999 < baseStart_7660999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7660999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661052 : List Nat := [2, 2, 2, 1, 2, 1, 4, 2, 2, 5]
def baseStart_7661052 : Nat := 118140960795 + 7661052 * 2 ^ 59
def prefixEnd_7661052 : Nat := 4983230072969 + 3 ^ 40 * 7661052 * 2
def baseEnd_7661052 : Nat := 1311267331696221777505823

theorem tailTrace_7661052 : CollatzResearch.WordTrace tailWord_7661052 prefixEnd_7661052 1311267331696221777505823 := by
  unfold tailWord_7661052
  simp only [CollatzResearch.WordTrace]
  refine ⟨139710760920662241179692705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186281014560882988239590273 139710760920662241179692705)
  ·
    refine ⟨104783070690496680884769529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139710760920662241179692705 104783070690496680884769529)
    ·
      refine ⟨78587303017872510663577147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104783070690496680884769529 78587303017872510663577147)
      ·
        refine ⟨117880954526808765995365721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78587303017872510663577147 117880954526808765995365721)
        ·
          refine ⟨88410715895106574496524291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117880954526808765995365721 88410715895106574496524291)
          ·
            refine ⟨132616073842659861744786437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88410715895106574496524291 132616073842659861744786437)
            ·
              refine ⟨24865513845498724077147457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132616073842659861744786437 24865513845498724077147457)
              ·
                refine ⟨18649135384124043057860593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24865513845498724077147457 18649135384124043057860593)
                ·
                  refine ⟨13986851538093032293395445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18649135384124043057860593 13986851538093032293395445)
                  ·
                    refine ⟨1311267331696221777505823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13986851538093032293395445 1311267331696221777505823)
                    ·
                      rfl

theorem cell23_7661052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_7661052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661052 prefixEnd_7661052 := by exact prefixLift 7661052
  have htrace : WordTrace (prefixWord ++ tailWord_7661052) baseStart_7661052 baseEnd_7661052 := by
    simpa [prefixWord, tailWord_7661052, baseEnd_7661052] using wordTrace_append hprefix tailTrace_7661052
  have hstable : (prefixWord ++ tailWord_7661052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661052).length < 2 ^ (prefixWord ++ tailWord_7661052).sum := by decide
  have hdescent : baseEnd_7661052 < baseStart_7661052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661089 : List Nat := [1, 2, 3, 2, 2, 2, 3, 1, 2, 1, 4]
def baseStart_7661089 : Nat := 118140960795 + 7661089 * 2 ^ 59
def prefixEnd_7661089 : Nat := 4983230072969 + 3 ^ 40 * 7661089 * 2
def baseEnd_7661089 : Nat := 3933820993872881687754799

theorem tailTrace_7661089 : CollatzResearch.WordTrace tailWord_7661089 prefixEnd_7661089 3933820993872881687754799 := by
  unfold tailWord_7661089
  simp only [CollatzResearch.WordTrace]
  refine ⟨279422871342190437678482321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186281914228126958452321547 279422871342190437678482321)
  ·
    refine ⟨209567153506642828258861741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279422871342190437678482321 209567153506642828258861741)
    ·
      refine ⟨78587682564991060597073153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209567153506642828258861741 78587682564991060597073153)
      ·
        refine ⟨58940761923743295447804865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78587682564991060597073153 58940761923743295447804865)
        ·
          refine ⟨44205571442807471585853649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58940761923743295447804865 44205571442807471585853649)
          ·
            refine ⟨33154178582105603689390237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44205571442807471585853649 33154178582105603689390237)
            ·
              refine ⟨12432816968289601383521339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33154178582105603689390237 12432816968289601383521339)
              ·
                refine ⟨18649225452434402075282009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12432816968289601383521339 18649225452434402075282009)
                ·
                  refine ⟨13986919089325801556461507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18649225452434402075282009 13986919089325801556461507)
                  ·
                    refine ⟨20980378633988702334692261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13986919089325801556461507 20980378633988702334692261)
                    ·
                      refine ⟨3933820993872881687754799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20980378633988702334692261 3933820993872881687754799)
                      ·
                        rfl

theorem cell23_7661089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_7661089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661089 prefixEnd_7661089 := by exact prefixLift 7661089
  have htrace : WordTrace (prefixWord ++ tailWord_7661089) baseStart_7661089 baseEnd_7661089 := by
    simpa [prefixWord, tailWord_7661089, baseEnd_7661089] using wordTrace_append hprefix tailTrace_7661089
  have hstable : (prefixWord ++ tailWord_7661089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661089).length < 2 ^ (prefixWord ++ tailWord_7661089).sum := by decide
  have hdescent : baseEnd_7661089 < baseStart_7661089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661112 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 8]
def baseStart_7661112 : Nat := 118140960795 + 7661112 * 2 ^ 59
def prefixEnd_7661112 : Nat := 4983230072969 + 3 ^ 40 * 7661112 * 2
def baseEnd_7661112 : Nat := 437092533769770566418577

theorem tailTrace_7661112 : CollatzResearch.WordTrace tailWord_7661112 prefixEnd_7661112 437092533769770566418577 := by
  unfold tailWord_7661112
  simp only [CollatzResearch.WordTrace]
  refine ⟨139711855110553556303284795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186282473480738075071046393 139711855110553556303284795)
  ·
    refine ⟨209567782665830334454927193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139711855110553556303284795 209567782665830334454927193)
    ·
      refine ⟨157175836999372750841195395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209567782665830334454927193 157175836999372750841195395)
      ·
        refine ⟨235763755499059126261793093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157175836999372750841195395 235763755499059126261793093)
        ·
          refine ⟨44205704156073586174086205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235763755499059126261793093 44205704156073586174086205)
          ·
            refine ⟨16577139058527594815282327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44205704156073586174086205 16577139058527594815282327)
            ·
              refine ⟨24865708587791392222923491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16577139058527594815282327 24865708587791392222923491)
              ·
                refine ⟨37298562881687088334385237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24865708587791392222923491 37298562881687088334385237)
                ·
                  refine ⟨437092533769770566418577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37298562881687088334385237 437092533769770566418577)
                  ·
                    rfl

theorem cell23_7661112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 8].length) (baseStart_7661112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661112 prefixEnd_7661112 := by exact prefixLift 7661112
  have htrace : WordTrace (prefixWord ++ tailWord_7661112) baseStart_7661112 baseEnd_7661112 := by
    simpa [prefixWord, tailWord_7661112, baseEnd_7661112] using wordTrace_append hprefix tailTrace_7661112
  have hstable : (prefixWord ++ tailWord_7661112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661112).length < 2 ^ (prefixWord ++ tailWord_7661112).sum := by decide
  have hdescent : baseEnd_7661112 < baseStart_7661112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661116 : List Nat := [2, 2, 2, 2, 4, 1, 2, 1, 3, 4]
def baseStart_7661116 : Nat := 118140960795 + 7661116 * 2 ^ 59
def prefixEnd_7661116 : Nat := 4983230072969 + 3 ^ 40 * 7661116 * 2
def baseEnd_7661116 : Nat := 1311278285950184360705725

theorem tailTrace_7661116 : CollatzResearch.WordTrace tailWord_7661116 prefixEnd_7661116 1311278285950184360705725 := by
  unfold tailWord_7661116
  simp only [CollatzResearch.WordTrace]
  refine ⟨139711928056546310644857601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186282570742061747526476801 139711928056546310644857601)
  ·
    refine ⟨104783946042409732983643201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139711928056546310644857601 104783946042409732983643201)
    ·
      refine ⟨78587959531807299737732401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104783946042409732983643201 78587959531807299737732401)
      ·
        refine ⟨58940969648855474803299301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78587959531807299737732401 58940969648855474803299301)
        ·
          refine ⟨11051431809160401525618619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58940969648855474803299301 11051431809160401525618619)
          ·
            refine ⟨16577147713740602288427929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11051431809160401525618619 16577147713740602288427929)
            ·
              refine ⟨12432860785305451716320947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16577147713740602288427929 12432860785305451716320947)
              ·
                refine ⟨18649291177958177574481421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12432860785305451716320947 18649291177958177574481421)
                ·
                  refine ⟨6993484191734316590430533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18649291177958177574481421 6993484191734316590430533)
                  ·
                    refine ⟨1311278285950184360705725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6993484191734316590430533 1311278285950184360705725)
                    ·
                      rfl

theorem cell23_7661116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_7661116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661116 prefixEnd_7661116 := by exact prefixLift 7661116
  have htrace : WordTrace (prefixWord ++ tailWord_7661116) baseStart_7661116 baseEnd_7661116 := by
    simpa [prefixWord, tailWord_7661116, baseEnd_7661116] using wordTrace_append hprefix tailTrace_7661116
  have hstable : (prefixWord ++ tailWord_7661116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661116).length < 2 ^ (prefixWord ++ tailWord_7661116).sum := by decide
  have hdescent : baseEnd_7661116 < baseStart_7661116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661159 : List Nat := [1, 1, 5, 1, 1, 1, 4, 3, 1, 5]
def baseStart_7661159 : Nat := 118140960795 + 7661159 * 2 ^ 59
def prefixEnd_7661159 : Nat := 4983230072969 + 3 ^ 40 * 7661159 * 2
def baseEnd_7661159 : Nat := 1311285645839565471293159

theorem tailTrace_7661159 : CollatzResearch.WordTrace tailWord_7661159 prefixEnd_7661159 1311285645839565471293159 := by
  unfold tailWord_7661159
  simp only [CollatzResearch.WordTrace]
  refine ⟨279425424451936839633530531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186283616301291226422353687 279425424451936839633530531)
  ·
    refine ⟨419138136677905259450295797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279425424451936839633530531 419138136677905259450295797)
    ·
      refine ⟨39294200313553618073465231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 419138136677905259450295797 39294200313553618073465231)
      ·
        refine ⟨58941300470330427110197847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39294200313553618073465231 58941300470330427110197847)
        ·
          refine ⟨88411950705495640665296771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58941300470330427110197847 88411950705495640665296771)
          ·
            refine ⟨132617926058243460997945157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88411950705495640665296771 132617926058243460997945157)
            ·
              refine ⟨24865861135920648937114717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132617926058243460997945157 24865861135920648937114717)
              ·
                refine ⟨9324697925970243351418019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24865861135920648937114717 9324697925970243351418019)
                ·
                  refine ⟨13987046888955365027127029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9324697925970243351418019 13987046888955365027127029)
                  ·
                    refine ⟨1311285645839565471293159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13987046888955365027127029 1311285645839565471293159)
                    ·
                      rfl

theorem cell23_7661159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_7661159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661159 prefixEnd_7661159 := by exact prefixLift 7661159
  have htrace : WordTrace (prefixWord ++ tailWord_7661159) baseStart_7661159 baseEnd_7661159 := by
    simpa [prefixWord, tailWord_7661159, baseEnd_7661159] using wordTrace_append hprefix tailTrace_7661159
  have hstable : (prefixWord ++ tailWord_7661159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661159).length < 2 ^ (prefixWord ++ tailWord_7661159).sum := by decide
  have hdescent : baseEnd_7661159 < baseStart_7661159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661173 : List Nat := [1, 3, 4, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_7661173 : Nat := 118140960795 + 7661173 * 2 ^ 59
def prefixEnd_7661173 : Nat := 4983230072969 + 3 ^ 40 * 7661173 * 2
def baseEnd_7661173 : Nat := 3933864126247859359104413

theorem tailTrace_7661173 : CollatzResearch.WordTrace tailWord_7661173 prefixEnd_7661173 3933864126247859359104413 := by
  unfold tailWord_7661173
  simp only [CollatzResearch.WordTrace]
  refine ⟨279425935073886120024540173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186283956715924080016360115 279425935073886120024540173)
  ·
    refine ⟨104784725652707295009202565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279425935073886120024540173 104784725652707295009202565)
    ·
      refine ⟨19647136059882617814225481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104784725652707295009202565 19647136059882617814225481)
      ·
        refine ⟨14735352044911963360669111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19647136059882617814225481 14735352044911963360669111)
        ·
          refine ⟨22103028067367945041003667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14735352044911963360669111 22103028067367945041003667)
          ·
            refine ⟨33154542101051917561505501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22103028067367945041003667 33154542101051917561505501)
            ·
              refine ⟨12432953287894469085564563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33154542101051917561505501 12432953287894469085564563)
              ·
                refine ⟨18649429931841703628346845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12432953287894469085564563 18649429931841703628346845)
                ·
                  refine ⟨6993536224440638860630067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18649429931841703628346845 6993536224440638860630067)
                  ·
                    refine ⟨10490304336660958290945101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6993536224440638860630067 10490304336660958290945101)
                    ·
                      refine ⟨3933864126247859359104413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10490304336660958290945101 3933864126247859359104413)
                      ·
                        rfl

theorem cell23_7661173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_7661173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661173 prefixEnd_7661173 := by exact prefixLift 7661173
  have htrace : WordTrace (prefixWord ++ tailWord_7661173) baseStart_7661173 baseEnd_7661173 := by
    simpa [prefixWord, tailWord_7661173, baseEnd_7661173] using wordTrace_append hprefix tailTrace_7661173
  have hstable : (prefixWord ++ tailWord_7661173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661173).length < 2 ^ (prefixWord ++ tailWord_7661173).sum := by decide
  have hdescent : baseEnd_7661173 < baseStart_7661173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661196 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 5, 2, 2]
def baseStart_7661196 : Nat := 118140960795 + 7661196 * 2 ^ 59
def prefixEnd_7661196 : Nat := 4983230072969 + 3 ^ 40 * 7661196 * 2
def baseEnd_7661196 : Nat := 3933875936302912769116807

theorem tailTrace_7661196 : CollatzResearch.WordTrace tailWord_7661196 prefixEnd_7661196 3933875936302912769116807 := by
  unfold tailWord_7661196
  simp only [CollatzResearch.WordTrace]
  refine ⟨139713386976401397476313721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186284515968535196635084961 139713386976401397476313721)
  ·
    refine ⟨104785040232301048107235291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139713386976401397476313721 104785040232301048107235291)
    ·
      refine ⟨157177560348451572160852937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104785040232301048107235291 157177560348451572160852937)
      ·
        refine ⟨117883170261338679120639703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157177560348451572160852937 117883170261338679120639703)
        ·
          refine ⟨176824755392008018680959555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117883170261338679120639703 176824755392008018680959555)
          ·
            refine ⟨265237133088012028021439333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176824755392008018680959555 265237133088012028021439333)
            ·
              refine ⟨49731962454002255254019875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265237133088012028021439333 49731962454002255254019875)
              ·
                refine ⟨74597943681003382881029813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49731962454002255254019875 74597943681003382881029813)
                ·
                  refine ⟨6993557220094067145096545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74597943681003382881029813 6993557220094067145096545)
                  ·
                    refine ⟨5245167915070550358822409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6993557220094067145096545 5245167915070550358822409)
                    ·
                      refine ⟨3933875936302912769116807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245167915070550358822409 3933875936302912769116807)
                      ·
                        rfl

theorem cell23_7661196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_7661196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661196 prefixEnd_7661196 := by exact prefixLift 7661196
  have htrace : WordTrace (prefixWord ++ tailWord_7661196) baseStart_7661196 baseEnd_7661196 := by
    simpa [prefixWord, tailWord_7661196, baseEnd_7661196] using wordTrace_append hprefix tailTrace_7661196
  have hstable : (prefixWord ++ tailWord_7661196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661196).length < 2 ^ (prefixWord ++ tailWord_7661196).sum := by decide
  have hdescent : baseEnd_7661196 < baseStart_7661196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661216 : List Nat := [2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 5]
def baseStart_7661216 : Nat := 118140960795 + 7661216 * 2 ^ 59
def prefixEnd_7661216 : Nat := 4983230072969 + 3 ^ 40 * 7661216 * 2
def baseEnd_7661216 : Nat := 3933886205916002690866715

theorem tailTrace_7661216 : CollatzResearch.WordTrace tailWord_7661216 prefixEnd_7661216 3933886205916002690866715 := by
  unfold tailWord_7661216
  simp only [CollatzResearch.WordTrace]
  refine ⟨139713751706365169184177751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186285002275153558912237001 139713751706365169184177751)
  ·
    refine ⟨209570627559547753776266627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139713751706365169184177751 209570627559547753776266627)
    ·
      refine ⟨314355941339321630664399941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209570627559547753776266627 314355941339321630664399941)
      ·
        refine ⟨58941739001122805749574989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314355941339321630664399941 58941739001122805749574989)
        ·
          refine ⟨22103152125421052156090621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58941739001122805749574989 22103152125421052156090621)
          ·
            refine ⟨8288682047032894558533983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22103152125421052156090621 8288682047032894558533983)
            ·
              refine ⟨12433023070549341837800975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8288682047032894558533983 12433023070549341837800975)
              ·
                refine ⟨18649534605824012756701463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12433023070549341837800975 18649534605824012756701463)
                ·
                  refine ⟨27974301908736019135052195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18649534605824012756701463 27974301908736019135052195)
                  ·
                    refine ⟨41961452863104028702578293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27974301908736019135052195 41961452863104028702578293)
                    ·
                      refine ⟨3933886205916002690866715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41961452863104028702578293 3933886205916002690866715)
                      ·
                        rfl

theorem cell23_7661216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_7661216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661216 prefixEnd_7661216 := by exact prefixLift 7661216
  have htrace : WordTrace (prefixWord ++ tailWord_7661216) baseStart_7661216 baseEnd_7661216 := by
    simpa [prefixWord, tailWord_7661216, baseEnd_7661216] using wordTrace_append hprefix tailTrace_7661216
  have hstable : (prefixWord ++ tailWord_7661216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661216).length < 2 ^ (prefixWord ++ tailWord_7661216).sum := by decide
  have hdescent : baseEnd_7661216 < baseStart_7661216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661224 : List Nat := [2, 1, 7, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_7661224 : Nat := 118140960795 + 7661224 * 2 ^ 59
def prefixEnd_7661224 : Nat := 4983230072969 + 3 ^ 40 * 7661224 * 2
def baseEnd_7661224 : Nat := 3933890313761238659566679

theorem tailTrace_7661224 : CollatzResearch.WordTrace tailWord_7661224 prefixEnd_7661224 3933890313761238659566679 := by
  unfold tailWord_7661224
  simp only [CollatzResearch.WordTrace]
  refine ⟨139713897598350677867323363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186285196797800903823097817 139713897598350677867323363)
  ·
    refine ⟨209570846397526016800985045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139713897598350677867323363 209570846397526016800985045)
    ·
      refine ⟨4911816712442016018773087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 209570846397526016800985045 4911816712442016018773087)
      ·
        refine ⟨7367725068663024028159631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4911816712442016018773087 7367725068663024028159631)
        ·
          refine ⟨11051587602994536042239447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7367725068663024028159631 11051587602994536042239447)
          ·
            refine ⟨16577381404491804063359171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11051587602994536042239447 16577381404491804063359171)
            ·
              refine ⟨24866072106737706095038757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16577381404491804063359171 24866072106737706095038757)
              ·
                refine ⟨4662388520013319892819767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24866072106737706095038757 4662388520013319892819767)
                ·
                  refine ⟨6993582780019979839229651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4662388520013319892819767 6993582780019979839229651)
                  ·
                    refine ⟨10490374170029969758844477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6993582780019979839229651 10490374170029969758844477)
                    ·
                      refine ⟨3933890313761238659566679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10490374170029969758844477 3933890313761238659566679)
                      ·
                        rfl

theorem cell23_7661224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_7661224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661224 prefixEnd_7661224 := by exact prefixLift 7661224
  have htrace : WordTrace (prefixWord ++ tailWord_7661224) baseStart_7661224 baseEnd_7661224 := by
    simpa [prefixWord, tailWord_7661224, baseEnd_7661224] using wordTrace_append hprefix tailTrace_7661224
  have hstable : (prefixWord ++ tailWord_7661224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661224).length < 2 ^ (prefixWord ++ tailWord_7661224).sum := by decide
  have hdescent : baseEnd_7661224 < baseStart_7661224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661232 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 2, 7]
def baseStart_7661232 : Nat := 118140960795 + 7661232 * 2 ^ 59
def prefixEnd_7661232 : Nat := 4983230072969 + 3 ^ 40 * 7661232 * 2
def baseEnd_7661232 : Nat := 1311298140535491542755547

theorem tailTrace_7661232 : CollatzResearch.WordTrace tailWord_7661232 prefixEnd_7661232 1311298140535491542755547 := by
  unfold tailWord_7661232
  simp only [CollatzResearch.WordTrace]
  refine ⟨139714043490336186550468975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186285391320448248733958633 139714043490336186550468975)
  ·
    refine ⟨209571065235504279825703463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139714043490336186550468975 209571065235504279825703463)
    ·
      refine ⟨314356597853256419738555195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209571065235504279825703463 314356597853256419738555195)
      ·
        refine ⟨471534896779884629607832793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314356597853256419738555195 471534896779884629607832793)
        ·
          refine ⟨353651172584913472205874595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471534896779884629607832793 353651172584913472205874595)
          ·
            refine ⟨530476758877370208308811893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353651172584913472205874595 530476758877370208308811893)
            ·
              refine ⟨49732196144753457028951115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 530476758877370208308811893 49732196144753457028951115)
              ·
                refine ⟨74598294217130185543426673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49732196144753457028951115 74598294217130185543426673)
                ·
                  refine ⟨55948720662847639157570005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74598294217130185543426673 55948720662847639157570005)
                  ·
                    refine ⟨1311298140535491542755547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55948720662847639157570005 1311298140535491542755547)
                    ·
                      rfl

theorem cell23_7661232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 2, 7].length) (baseStart_7661232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661232 prefixEnd_7661232 := by exact prefixLift 7661232
  have htrace : WordTrace (prefixWord ++ tailWord_7661232) baseStart_7661232 baseEnd_7661232 := by
    simpa [prefixWord, tailWord_7661232, baseEnd_7661232] using wordTrace_append hprefix tailTrace_7661232
  have hstable : (prefixWord ++ tailWord_7661232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661232).length < 2 ^ (prefixWord ++ tailWord_7661232).sum := by decide
  have hdescent : baseEnd_7661232 < baseStart_7661232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661246 : List Nat := [4, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_7661246 : Nat := 118140960795 + 7661246 * 2 ^ 59
def prefixEnd_7661246 : Nat := 4983230072969 + 3 ^ 40 * 7661246 * 2
def baseEnd_7661246 : Nat := 3933901610335637573491577

theorem tailTrace_7661246 : CollatzResearch.WordTrace tailWord_7661246 prefixEnd_7661246 3933901610335637573491577 := by
  unfold tailWord_7661246
  simp only [CollatzResearch.WordTrace]
  refine ⟨34928574700327706686493449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186285731735081102327965061 34928574700327706686493449)
  ·
    refine ⟨26196431025245780014870087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34928574700327706686493449 26196431025245780014870087)
    ·
      refine ⟨39294646537868670022305131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26196431025245780014870087 39294646537868670022305131)
      ·
        refine ⟨58941969806803005033457697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39294646537868670022305131 58941969806803005033457697)
        ·
          refine ⟨44206477355102253775093273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58941969806803005033457697 44206477355102253775093273)
          ·
            refine ⟨33154858016326690331319955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44206477355102253775093273 33154858016326690331319955)
            ·
              refine ⟨49732287024490035496979933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33154858016326690331319955 49732287024490035496979933)
              ·
                refine ⟨18649607634183763311367475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49732287024490035496979933 18649607634183763311367475)
                ·
                  refine ⟨27974411451275644967051213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18649607634183763311367475 27974411451275644967051213)
                  ·
                    refine ⟨10490404294228366862644205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27974411451275644967051213 10490404294228366862644205)
                    ·
                      refine ⟨3933901610335637573491577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10490404294228366862644205 3933901610335637573491577)
                      ·
                        rfl

theorem cell23_7661246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_7661246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661246 prefixEnd_7661246 := by exact prefixLift 7661246
  have htrace : WordTrace (prefixWord ++ tailWord_7661246) baseStart_7661246 baseEnd_7661246 := by
    simpa [prefixWord, tailWord_7661246, baseEnd_7661246] using wordTrace_append hprefix tailTrace_7661246
  have hstable : (prefixWord ++ tailWord_7661246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661246).length < 2 ^ (prefixWord ++ tailWord_7661246).sum := by decide
  have hdescent : baseEnd_7661246 < baseStart_7661246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661256 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 3, 3, 2]
def baseStart_7661256 : Nat := 118140960795 + 7661256 * 2 ^ 59
def prefixEnd_7661256 : Nat := 4983230072969 + 3 ^ 40 * 7661256 * 2
def baseEnd_7661256 : Nat := 3933906745142182534366531

theorem tailTrace_7661256 : CollatzResearch.WordTrace tailWord_7661256 prefixEnd_7661256 3933906745142182534366531 := by
  unfold tailWord_7661256
  simp only [CollatzResearch.WordTrace]
  refine ⟨139714481166292712599905811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186285974888390283466541081 139714481166292712599905811)
  ·
    refine ⟨209571721749439068899858717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139714481166292712599905811 209571721749439068899858717)
    ·
      refine ⟨78589395656039650837447019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209571721749439068899858717 78589395656039650837447019)
      ·
        refine ⟨117884093484059476256170529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78589395656039650837447019 117884093484059476256170529)
        ·
          refine ⟨88413070113044607192127897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117884093484059476256170529 88413070113044607192127897)
          ·
            refine ⟨66309802584783455394095923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88413070113044607192127897 66309802584783455394095923)
            ·
              refine ⟨99464703877175183091143885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66309802584783455394095923 99464703877175183091143885)
              ·
                refine ⟨37299263953940693659178957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99464703877175183091143885 37299263953940693659178957)
                ·
                  refine ⟨13987223982727760122192109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37299263953940693659178957 13987223982727760122192109)
                  ·
                    refine ⟨5245208993522910045822041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13987223982727760122192109 5245208993522910045822041)
                    ·
                      refine ⟨3933906745142182534366531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245208993522910045822041 3933906745142182534366531)
                      ·
                        rfl

theorem cell23_7661256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_7661256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661256 prefixEnd_7661256 := by exact prefixLift 7661256
  have htrace : WordTrace (prefixWord ++ tailWord_7661256) baseStart_7661256 baseEnd_7661256 := by
    simpa [prefixWord, tailWord_7661256, baseEnd_7661256] using wordTrace_append hprefix tailTrace_7661256
  have hstable : (prefixWord ++ tailWord_7661256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661256).length < 2 ^ (prefixWord ++ tailWord_7661256).sum := by decide
  have hdescent : baseEnd_7661256 < baseStart_7661256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661273 : List Nat := [1, 2, 1, 2, 3, 4, 1, 3, 1, 3, 2]
def baseStart_7661273 : Nat := 118140960795 + 7661273 * 2 ^ 59
def prefixEnd_7661273 : Nat := 4983230072969 + 3 ^ 40 * 7661273 * 2
def baseEnd_7661273 : Nat := 3933915474313308967853953

theorem tailTrace_7661273 : CollatzResearch.WordTrace tailWord_7661273 prefixEnd_7661273 3933915474313308967853953 := by
  unfold tailWord_7661273
  simp only [CollatzResearch.WordTrace]
  refine ⟨279429582373523837103180473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186286388249015891402120315 279429582373523837103180473)
  ·
    refine ⟨209572186780142877827385355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279429582373523837103180473 209572186780142877827385355)
    ·
      refine ⟨314358280170214316741078033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209572186780142877827385355 314358280170214316741078033)
      ·
        refine ⟨235768710127660737555808525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314358280170214316741078033 235768710127660737555808525)
        ·
          refine ⟨88413266297872776583428197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235768710127660737555808525 88413266297872776583428197)
          ·
            refine ⟨16577487430851145609392787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88413266297872776583428197 16577487430851145609392787)
            ·
              refine ⟨24866231146276718414089181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16577487430851145609392787 24866231146276718414089181)
              ·
                refine ⟨9324836679853769405283443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24866231146276718414089181 9324836679853769405283443)
                ·
                  refine ⟨13987255019780654107925165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9324836679853769405283443 13987255019780654107925165)
                  ·
                    refine ⟨5245220632417745290471937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13987255019780654107925165 5245220632417745290471937)
                    ·
                      refine ⟨3933915474313308967853953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245220632417745290471937 3933915474313308967853953)
                      ·
                        rfl

theorem cell23_7661273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 3, 2].length) (baseStart_7661273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661273 prefixEnd_7661273 := by exact prefixLift 7661273
  have htrace : WordTrace (prefixWord ++ tailWord_7661273) baseStart_7661273 baseEnd_7661273 := by
    simpa [prefixWord, tailWord_7661273, baseEnd_7661273] using wordTrace_append hprefix tailTrace_7661273
  have hstable : (prefixWord ++ tailWord_7661273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661273).length < 2 ^ (prefixWord ++ tailWord_7661273).sum := by decide
  have hdescent : baseEnd_7661273 < baseStart_7661273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661299 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 4]
def baseStart_7661299 : Nat := 118140960795 + 7661299 * 2 ^ 59
def prefixEnd_7661299 : Nat := 4983230072969 + 3 ^ 40 * 7661299 * 2
def baseEnd_7661299 : Nat := 3933928824810325866128833

theorem tailTrace_7661299 : CollatzResearch.WordTrace tailWord_7661299 prefixEnd_7661299 3933928824810325866128833 := by
  unfold tailWord_7661299
  simp only [CollatzResearch.WordTrace]
  refine ⟨279430530671429643543626951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186287020447619762362417967 279430530671429643543626951)
  ·
    refine ⟨419145796007144465315440427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279430530671429643543626951 419145796007144465315440427)
    ·
      refine ⟨628718694010716697973160641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419145796007144465315440427 628718694010716697973160641)
      ·
        refine ⟨471539020508037523479870481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628718694010716697973160641 471539020508037523479870481)
        ·
          refine ⟨353654265381028142609902861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471539020508037523479870481 353654265381028142609902861)
          ·
            refine ⟨132620349517885553478713573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353654265381028142609902861 132620349517885553478713573)
            ·
              refine ⟨24866315534603541277258795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132620349517885553478713573 24866315534603541277258795)
              ·
                refine ⟨37299473301905311915888193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24866315534603541277258795 37299473301905311915888193)
                ·
                  refine ⟨27974604976428983936916145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37299473301905311915888193 27974604976428983936916145)
                  ·
                    refine ⟨20980953732321737952687109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27974604976428983936916145 20980953732321737952687109)
                    ·
                      refine ⟨3933928824810325866128833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20980953732321737952687109 3933928824810325866128833)
                      ·
                        rfl

theorem cell23_7661299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_7661299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661299 prefixEnd_7661299 := by exact prefixLift 7661299
  have htrace : WordTrace (prefixWord ++ tailWord_7661299) baseStart_7661299 baseEnd_7661299 := by
    simpa [prefixWord, tailWord_7661299, baseEnd_7661299] using wordTrace_append hprefix tailTrace_7661299
  have hstable : (prefixWord ++ tailWord_7661299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661299).length < 2 ^ (prefixWord ++ tailWord_7661299).sum := by decide
  have hdescent : baseEnd_7661299 < baseStart_7661299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661303 : List Nat := [1, 1, 3, 1, 1, 1, 4, 5, 2, 2, 2]
def baseStart_7661303 : Nat := 118140960795 + 7661303 * 2 ^ 59
def prefixEnd_7661303 : Nat := 4983230072969 + 3 ^ 40 * 7661303 * 2
def baseEnd_7661303 : Nat := 3933930878732943850478815

theorem tailTrace_7661303 : CollatzResearch.WordTrace tailWord_7661303 prefixEnd_7661303 3933930878732943850478815 := by
  unfold tailWord_7661303
  simp only [CollatzResearch.WordTrace]
  refine ⟨279430676563415152226772563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186287117708943434817848375 279430676563415152226772563)
  ·
    refine ⟨419146014845122728340158845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279430676563415152226772563 419146014845122728340158845)
    ·
      refine ⟨157179755566921023127559567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419146014845122728340158845 157179755566921023127559567)
      ·
        refine ⟨235769633350381534691339351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157179755566921023127559567 235769633350381534691339351)
        ·
          refine ⟨353654450025572302037009027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235769633350381534691339351 353654450025572302037009027)
          ·
            refine ⟨530481675038358453055513541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353654450025572302037009027 530481675038358453055513541)
            ·
              refine ⟨99465314069692209947908789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 530481675038358453055513541 99465314069692209947908789)
              ·
                refine ⟨9324873194033644682616449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99465314069692209947908789 9324873194033644682616449)
                ·
                  refine ⟨6993654895525233511962337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9324873194033644682616449 6993654895525233511962337)
                  ·
                    refine ⟨5245241171643925133971753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6993654895525233511962337 5245241171643925133971753)
                    ·
                      refine ⟨3933930878732943850478815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245241171643925133971753 3933930878732943850478815)
                      ·
                        rfl

theorem cell23_7661303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 2, 2].length) (baseStart_7661303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661303 prefixEnd_7661303 := by exact prefixLift 7661303
  have htrace : WordTrace (prefixWord ++ tailWord_7661303) baseStart_7661303 baseEnd_7661303 := by
    simpa [prefixWord, tailWord_7661303, baseEnd_7661303] using wordTrace_append hprefix tailTrace_7661303
  have hstable : (prefixWord ++ tailWord_7661303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661303).length < 2 ^ (prefixWord ++ tailWord_7661303).sum := by decide
  have hdescent : baseEnd_7661303 < baseStart_7661303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661339 : List Nat := [1, 1, 1, 1, 1, 1, 4, 6, 2, 5]
def baseStart_7661339 : Nat := 118140960795 + 7661339 * 2 ^ 59
def prefixEnd_7661339 : Nat := 4983230072969 + 3 ^ 40 * 7661339 * 2
def baseEnd_7661339 : Nat := 1311316454678835236542883

theorem tailTrace_7661339 : CollatzResearch.WordTrace tailWord_7661339 prefixEnd_7661339 1311316454678835236542883 := by
  unfold tailWord_7661339
  simp only [CollatzResearch.WordTrace]
  refine ⟨279431989591284730375083071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186287993060856486916722047 279431989591284730375083071)
  ·
    refine ⟨419147984386927095562624607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279431989591284730375083071 419147984386927095562624607)
    ·
      refine ⟨628721976580390643343936911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419147984386927095562624607 628721976580390643343936911)
      ·
        refine ⟨943082964870585965015905367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628721976580390643343936911 943082964870585965015905367)
        ·
          refine ⟨1414624447305878947523858051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943082964870585965015905367 1414624447305878947523858051)
          ·
            refine ⟨2121936670958818421285787077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1414624447305878947523858051 2121936670958818421285787077)
            ·
              refine ⟨397863125804778453991085077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2121936670958818421285787077 397863125804778453991085077)
              ·
                refine ⟨18649834022098990030832113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 397863125804778453991085077 18649834022098990030832113)
                ·
                  refine ⟨13987375516574242523124085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18649834022098990030832113 13987375516574242523124085)
                  ·
                    refine ⟨1311316454678835236542883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13987375516574242523124085 1311316454678835236542883)
                    ·
                      rfl

theorem cell23_7661339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 5].length) (baseStart_7661339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661339 prefixEnd_7661339 := by exact prefixLift 7661339
  have htrace : WordTrace (prefixWord ++ tailWord_7661339) baseStart_7661339 baseEnd_7661339 := by
    simpa [prefixWord, tailWord_7661339, baseEnd_7661339] using wordTrace_append hprefix tailTrace_7661339
  have hstable : (prefixWord ++ tailWord_7661339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661339).length < 2 ^ (prefixWord ++ tailWord_7661339).sum := by decide
  have hdescent : baseEnd_7661339 < baseStart_7661339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661343 : List Nat := [1, 1, 2, 4, 2, 1, 5, 2, 5]
def baseStart_7661343 : Nat := 118140960795 + 7661343 * 2 ^ 59
def prefixEnd_7661343 : Nat := 4983230072969 + 3 ^ 40 * 7661343 * 2
def baseEnd_7661343 : Nat := 437105713106569299330959

theorem tailTrace_7661343 : CollatzResearch.WordTrace tailWord_7661343 prefixEnd_7661343 437105713106569299330959 := by
  unfold tailWord_7661343
  simp only [CollatzResearch.WordTrace]
  refine ⟨279432135483270239058228683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186288090322180159372152455 279432135483270239058228683)
  ·
    refine ⟨419148203224905358587343025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279432135483270239058228683 419148203224905358587343025)
    ·
      refine ⟨314361152418679018940507269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419148203224905358587343025 314361152418679018940507269)
      ·
        refine ⟨58942716078502316051345113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314361152418679018940507269 58942716078502316051345113)
        ·
          refine ⟨44207037058876737038508835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58942716078502316051345113 44207037058876737038508835)
          ·
            refine ⟨66310555588315105557763253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44207037058876737038508835 66310555588315105557763253)
            ·
              refine ⟨6216614586404541146040305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66310555588315105557763253 6216614586404541146040305)
              ·
                refine ⟨4662460939803405859530229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6216614586404541146040305 4662460939803405859530229)
                ·
                  refine ⟨437105713106569299330959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4662460939803405859530229 437105713106569299330959)
                  ·
                    rfl

theorem cell23_7661343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 5].length) (baseStart_7661343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661343 prefixEnd_7661343 := by exact prefixLift 7661343
  have htrace : WordTrace (prefixWord ++ tailWord_7661343) baseStart_7661343 baseEnd_7661343 := by
    simpa [prefixWord, tailWord_7661343, baseEnd_7661343] using wordTrace_append hprefix tailTrace_7661343
  have hstable : (prefixWord ++ tailWord_7661343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661343).length < 2 ^ (prefixWord ++ tailWord_7661343).sum := by decide
  have hdescent : baseEnd_7661343 < baseStart_7661343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661349 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 1, 1, 7]
def baseStart_7661349 : Nat := 118140960795 + 7661349 * 2 ^ 59
def prefixEnd_7661349 : Nat := 4983230072969 + 3 ^ 40 * 7661349 * 2
def baseEnd_7661349 : Nat := 3933954498843050670503603

theorem tailTrace_7661349 : CollatzResearch.WordTrace tailWord_7661349 prefixEnd_7661349 3933954498843050670503603 := by
  unfold tailWord_7661349
  simp only [CollatzResearch.WordTrace]
  refine ⟨279432354321248502082947101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186288236214165668055298067 279432354321248502082947101)
  ·
    refine ⟨104787132870468188281105163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279432354321248502082947101 104787132870468188281105163)
    ·
      refine ⟨157180699305702282421657745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104787132870468188281105163 157180699305702282421657745)
      ·
        refine ⟨117885524479276711816243309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157180699305702282421657745 117885524479276711816243309)
        ·
          refine ⟨44207071679728766931091241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117885524479276711816243309 44207071679728766931091241)
          ·
            refine ⟨33155303759796575198318431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44207071679728766931091241 33155303759796575198318431)
            ·
              refine ⟨49732955639694862797477647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33155303759796575198318431 49732955639694862797477647)
              ·
                refine ⟨74599433459542294196216471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49732955639694862797477647 74599433459542294196216471)
                ·
                  refine ⟨111899150189313441294324707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74599433459542294196216471 111899150189313441294324707)
                  ·
                    refine ⟨167848725283970161941487061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111899150189313441294324707 167848725283970161941487061)
                    ·
                      refine ⟨3933954498843050670503603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167848725283970161941487061 3933954498843050670503603)
                      ·
                        rfl

theorem cell23_7661349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_7661349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661349 prefixEnd_7661349 := by exact prefixLift 7661349
  have htrace : WordTrace (prefixWord ++ tailWord_7661349) baseStart_7661349 baseEnd_7661349 := by
    simpa [prefixWord, tailWord_7661349, baseEnd_7661349] using wordTrace_append hprefix tailTrace_7661349
  have hstable : (prefixWord ++ tailWord_7661349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661349).length < 2 ^ (prefixWord ++ tailWord_7661349).sum := by decide
  have hdescent : baseEnd_7661349 < baseStart_7661349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661373 : List Nat := [1, 4, 1, 4, 1, 2, 2, 1, 2, 5]
def baseStart_7661373 : Nat := 118140960795 + 7661373 * 2 ^ 59
def prefixEnd_7661373 : Nat := 4983230072969 + 3 ^ 40 * 7661373 * 2
def baseEnd_7661373 : Nat := 1311322274126252858867831

theorem tailTrace_7661373 : CollatzResearch.WordTrace tailWord_7661373 prefixEnd_7661373 1311322274126252858867831 := by
  unfold tailWord_7661373
  simp only [CollatzResearch.WordTrace]
  refine ⟨279433229673161554181820773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186288819782107702787880515 279433229673161554181820773)
  ·
    refine ⟨52393730563717791409091395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279433229673161554181820773 52393730563717791409091395)
    ·
      refine ⟨78590595845576687113637093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52393730563717791409091395 78590595845576687113637093)
      ·
        refine ⟨14735736721045628833806955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78590595845576687113637093 14735736721045628833806955)
        ·
          refine ⟨22103605081568443250710433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14735736721045628833806955 22103605081568443250710433)
          ·
            refine ⟨16577703811176332438032825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22103605081568443250710433 16577703811176332438032825)
            ·
              refine ⟨12433277858382249328524619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16577703811176332438032825 12433277858382249328524619)
              ·
                refine ⟨18649916787573373992786929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12433277858382249328524619 18649916787573373992786929)
                ·
                  refine ⟨13987437590680030494590197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18649916787573373992786929 13987437590680030494590197)
                  ·
                    refine ⟨1311322274126252858867831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13987437590680030494590197 1311322274126252858867831)
                    ·
                      rfl

theorem cell23_7661373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_7661373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661373 prefixEnd_7661373 := by exact prefixLift 7661373
  have htrace : WordTrace (prefixWord ++ tailWord_7661373) baseStart_7661373 baseEnd_7661373 := by
    simpa [prefixWord, tailWord_7661373, baseEnd_7661373] using wordTrace_append hprefix tailTrace_7661373
  have hstable : (prefixWord ++ tailWord_7661373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661373).length < 2 ^ (prefixWord ++ tailWord_7661373).sum := by decide
  have hdescent : baseEnd_7661373 < baseStart_7661373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661376 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 6, 4, 2]
def baseStart_7661376 : Nat := 118140960795 + 7661376 * 2 ^ 59
def prefixEnd_7661376 : Nat := 4983230072969 + 3 ^ 40 * 7661376 * 2
def baseEnd_7661376 : Nat := 3933968362820722064865979

theorem tailTrace_7661376 : CollatzResearch.WordTrace tailWord_7661376 prefixEnd_7661376 3933968362820722064865979 := by
  unfold tailWord_7661376
  simp only [CollatzResearch.WordTrace]
  refine ⟨139716669546075342847089991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186288892728100457129453321 139716669546075342847089991)
  ·
    refine ⟨209575004319113014270634987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139716669546075342847089991 209575004319113014270634987)
    ·
      refine ⟨314362506478669521405952481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209575004319113014270634987 314362506478669521405952481)
      ·
        refine ⟨235771879859002141054464361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314362506478669521405952481 235771879859002141054464361)
        ·
          refine ⟨176828909894251605790848271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235771879859002141054464361 176828909894251605790848271)
          ·
            refine ⟨265243364841377408686272407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176828909894251605790848271 265243364841377408686272407)
            ·
              refine ⟨397865047262066113029408611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265243364841377408686272407 397865047262066113029408611)
              ·
                refine ⟨596797570893099169544112917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397865047262066113029408611 596797570893099169544112917)
                ·
                  refine ⟨27974886135614023572380293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 596797570893099169544112917 27974886135614023572380293)
                  ·
                    refine ⟨5245291150427629419821305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27974886135614023572380293 5245291150427629419821305)
                    ·
                      refine ⟨3933968362820722064865979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245291150427629419821305 3933968362820722064865979)
                      ·
                        rfl

theorem cell23_7661376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 6, 4, 2].length) (baseStart_7661376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661376 prefixEnd_7661376 := by exact prefixLift 7661376
  have htrace : WordTrace (prefixWord ++ tailWord_7661376) baseStart_7661376 baseEnd_7661376 := by
    simpa [prefixWord, tailWord_7661376, baseEnd_7661376] using wordTrace_append hprefix tailTrace_7661376
  have hstable : (prefixWord ++ tailWord_7661376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661376).length < 2 ^ (prefixWord ++ tailWord_7661376).sum := by decide
  have hdescent : baseEnd_7661376 < baseStart_7661376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661410 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_7661410 : Nat := 118140960795 + 7661410 * 2 ^ 59
def prefixEnd_7661410 : Nat := 4983230072969 + 3 ^ 40 * 7661410 * 2
def baseEnd_7661410 : Nat := 3933985821162974931840823

theorem tailTrace_7661410 : CollatzResearch.WordTrace tailWord_7661410 prefixEnd_7661410 3933985821162974931840823 := by
  unfold tailWord_7661410
  simp only [CollatzResearch.WordTrace]
  refine ⟨69858644793506877375229421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186289719449351673000611789 69858644793506877375229421)
  ·
    refine ⟨26196991797565079015711033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69858644793506877375229421 26196991797565079015711033)
    ·
      refine ⟨19647743848173809261783275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26196991797565079015711033 19647743848173809261783275)
      ·
        refine ⟨29471615772260713892674913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19647743848173809261783275 29471615772260713892674913)
        ·
          refine ⟨22103711829195535419506185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29471615772260713892674913 22103711829195535419506185)
          ·
            refine ⟨16577783871896651564629639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22103711829195535419506185 16577783871896651564629639)
            ·
              refine ⟨24866675807844977346944459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16577783871896651564629639 24866675807844977346944459)
              ·
                refine ⟨37300013711767466020416689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24866675807844977346944459 37300013711767466020416689)
                ·
                  refine ⟨27975010283825599515312517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37300013711767466020416689 27975010283825599515312517)
                  ·
                    refine ⟨5245314428217299909121097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27975010283825599515312517 5245314428217299909121097)
                    ·
                      refine ⟨3933985821162974931840823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245314428217299909121097 3933985821162974931840823)
                      ·
                        rfl

theorem cell23_7661410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_7661410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661410 prefixEnd_7661410 := by exact prefixLift 7661410
  have htrace : WordTrace (prefixWord ++ tailWord_7661410) baseStart_7661410 baseEnd_7661410 := by
    simpa [prefixWord, tailWord_7661410, baseEnd_7661410] using wordTrace_append hprefix tailTrace_7661410
  have hstable : (prefixWord ++ tailWord_7661410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661410).length < 2 ^ (prefixWord ++ tailWord_7661410).sum := by decide
  have hdescent : baseEnd_7661410 < baseStart_7661410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661416 : List Nat := [2, 1, 4, 2, 1, 1, 1, 5, 6]
def baseStart_7661416 : Nat := 118140960795 + 7661416 * 2 ^ 59
def prefixEnd_7661416 : Nat := 4983230072969 + 3 ^ 40 * 7661416 * 2
def baseEnd_7661416 : Nat := 437109878005211323151755

theorem tailTrace_7661416 : CollatzResearch.WordTrace tailWord_7661416 prefixEnd_7661416 437109878005211323151755 := by
  unfold tailWord_7661416
  simp only [CollatzResearch.WordTrace]
  refine ⟨139717399006002886262818051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186289865341337181683757401 139717399006002886262818051)
  ·
    refine ⟨209576098509004329394227077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139717399006002886262818051 209576098509004329394227077)
    ·
      refine ⟨39295518470438311761417577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209576098509004329394227077 39295518470438311761417577)
      ·
        refine ⟨29471638852828733821063183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39295518470438311761417577 29471638852828733821063183)
        ·
          refine ⟨44207458279243100731594775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29471638852828733821063183 44207458279243100731594775)
          ·
            refine ⟨66311187418864651097392163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44207458279243100731594775 66311187418864651097392163)
            ·
              refine ⟨99466781128296976646088245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66311187418864651097392163 99466781128296976646088245)
              ·
                refine ⟨9325010730777841560570773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99466781128296976646088245 9325010730777841560570773)
                ·
                  refine ⟨437109878005211323151755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9325010730777841560570773 437109878005211323151755)
                  ·
                    rfl

theorem cell23_7661416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 6].length) (baseStart_7661416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661416 prefixEnd_7661416 := by exact prefixLift 7661416
  have htrace : WordTrace (prefixWord ++ tailWord_7661416) baseStart_7661416 baseEnd_7661416 := by
    simpa [prefixWord, tailWord_7661416, baseEnd_7661416] using wordTrace_append hprefix tailTrace_7661416
  have hstable : (prefixWord ++ tailWord_7661416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661416).length < 2 ^ (prefixWord ++ tailWord_7661416).sum := by decide
  have hdescent : baseEnd_7661416 < baseStart_7661416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661430 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_7661430 : Nat := 118140960795 + 7661430 * 2 ^ 59
def prefixEnd_7661430 : Nat := 4983230072969 + 3 ^ 40 * 7661430 * 2
def baseEnd_7661430 : Nat := 3933996090776064853590731

theorem tailTrace_7661430 : CollatzResearch.WordTrace tailWord_7661430 prefixEnd_7661430 3933996090776064853590731 := by
  unfold tailWord_7661430
  simp only [CollatzResearch.WordTrace]
  refine ⟨17464706789622190807290359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186290205755970035277763829 17464706789622190807290359)
  ·
    refine ⟨26197060184433286210935539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17464706789622190807290359 26197060184433286210935539)
    ·
      refine ⟨39295590276649929316403309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26197060184433286210935539 39295590276649929316403309)
      ·
        refine ⟨14735846353743723493651241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39295590276649929316403309 14735846353743723493651241)
        ·
          refine ⟨11051884765307792620238431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14735846353743723493651241 11051884765307792620238431)
          ·
            refine ⟨16577827147961688930357647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11051884765307792620238431 16577827147961688930357647)
            ·
              refine ⟨24866740721942533395536471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16577827147961688930357647 24866740721942533395536471)
              ·
                refine ⟨37300111082913800093304707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24866740721942533395536471 37300111082913800093304707)
                ·
                  refine ⟨55950166624370700139957061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37300111082913800093304707 55950166624370700139957061)
                  ·
                    refine ⟨10490656242069506276241949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55950166624370700139957061 10490656242069506276241949)
                    ·
                      refine ⟨3933996090776064853590731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10490656242069506276241949 3933996090776064853590731)
                      ·
                        rfl

theorem cell23_7661430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_7661430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661430 prefixEnd_7661430 := by exact prefixLift 7661430
  have htrace : WordTrace (prefixWord ++ tailWord_7661430) baseStart_7661430 baseEnd_7661430 := by
    simpa [prefixWord, tailWord_7661430, baseEnd_7661430] using wordTrace_append hprefix tailTrace_7661430
  have hstable : (prefixWord ++ tailWord_7661430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661430).length < 2 ^ (prefixWord ++ tailWord_7661430).sum := by decide
  have hdescent : baseEnd_7661430 < baseStart_7661430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661439 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 5]
def baseStart_7661439 : Nat := 118140960795 + 7661439 * 2 ^ 59
def prefixEnd_7661439 : Nat := 4983230072969 + 3 ^ 40 * 7661439 * 2
def baseEnd_7661439 : Nat := 3934000712101955318378189

theorem tailTrace_7661439 : CollatzResearch.WordTrace tailWord_7661439 prefixEnd_7661439 3934000712101955318378189 := by
  unfold tailWord_7661439
  simp only [CollatzResearch.WordTrace]
  refine ⟨279435636890922447453723371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186290424593948298302482247 279435636890922447453723371)
  ·
    refine ⟨419153455336383671180585057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279435636890922447453723371 419153455336383671180585057)
    ·
      refine ⟨314365091502287753385438793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419153455336383671180585057 314365091502287753385438793)
      ·
        refine ⟨235773818626715815039079095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314365091502287753385438793 235773818626715815039079095)
        ·
          refine ⟨353660727940073722558618643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235773818626715815039079095 353660727940073722558618643)
          ·
            refine ⟨530491091910110583837927965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353660727940073722558618643 530491091910110583837927965)
            ·
              refine ⟨198934159466291468939222987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 530491091910110583837927965 198934159466291468939222987)
              ·
                refine ⟨298401239199437203408834481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198934159466291468939222987 298401239199437203408834481)
                ·
                  refine ⟨223800929399577902556625861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298401239199437203408834481 223800929399577902556625861)
                  ·
                    refine ⟨41962674262420856729367349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 223800929399577902556625861 41962674262420856729367349)
                    ·
                      refine ⟨3934000712101955318378189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41962674262420856729367349 3934000712101955318378189)
                      ·
                        rfl

theorem cell23_7661439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_7661439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661439 prefixEnd_7661439 := by exact prefixLift 7661439
  have htrace : WordTrace (prefixWord ++ tailWord_7661439) baseStart_7661439 baseEnd_7661439 := by
    simpa [prefixWord, tailWord_7661439, baseEnd_7661439] using wordTrace_append hprefix tailTrace_7661439
  have hstable : (prefixWord ++ tailWord_7661439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661439).length < 2 ^ (prefixWord ++ tailWord_7661439).sum := by decide
  have hdescent : baseEnd_7661439 < baseStart_7661439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661450 : List Nat := [3, 1, 2, 4, 2, 2, 1, 2, 6]
def baseStart_7661450 : Nat := 118140960795 + 7661450 * 2 ^ 59
def prefixEnd_7661450 : Nat := 4983230072969 + 3 ^ 40 * 7661450 * 2
def baseEnd_7661450 : Nat := 437111817821017197260071

theorem tailTrace_7661450 : CollatzResearch.WordTrace tailWord_7661450 prefixEnd_7661450 437111817821017197260071 := by
  unfold tailWord_7661450
  simp only [CollatzResearch.WordTrace]
  refine ⟨69859009523470649083093451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186290692062588397554915869 69859009523470649083093451)
  ·
    refine ⟨104788514285205973624640177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69859009523470649083093451 104788514285205973624640177)
    ·
      refine ⟨78591385713904480218480133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104788514285205973624640177 78591385713904480218480133)
      ·
        refine ⟨14735884821357090040965025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78591385713904480218480133 14735884821357090040965025)
        ·
          refine ⟨11051913616017817530723769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14735884821357090040965025 11051913616017817530723769)
          ·
            refine ⟨8288935212013363148042827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11051913616017817530723769 8288935212013363148042827)
            ·
              refine ⟨12433402818020044722064241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8288935212013363148042827 12433402818020044722064241)
              ·
                refine ⟨9325052113515033541548181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12433402818020044722064241 9325052113515033541548181)
                ·
                  refine ⟨437111817821017197260071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9325052113515033541548181 437111817821017197260071)
                  ·
                    rfl

theorem cell23_7661450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 6].length) (baseStart_7661450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661450 prefixEnd_7661450 := by exact prefixLift 7661450
  have htrace : WordTrace (prefixWord ++ tailWord_7661450) baseStart_7661450 baseEnd_7661450 := by
    simpa [prefixWord, tailWord_7661450, baseEnd_7661450] using wordTrace_append hprefix tailTrace_7661450
  have hstable : (prefixWord ++ tailWord_7661450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661450).length < 2 ^ (prefixWord ++ tailWord_7661450).sum := by decide
  have hdescent : baseEnd_7661450 < baseStart_7661450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661460 : List Nat := [2, 4, 2, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_7661460 : Nat := 118140960795 + 7661460 * 2 ^ 59
def prefixEnd_7661460 : Nat := 4983230072969 + 3 ^ 40 * 7661460 * 2
def baseEnd_7661460 : Nat := 3934011495195699736215593

theorem tailTrace_7661460 : CollatzResearch.WordTrace tailWord_7661460 prefixEnd_7661460 3934011495195699736215593 := by
  unfold tailWord_7661460
  simp only [CollatzResearch.WordTrace]
  refine ⟨139718201411923184020118917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186290935215897578693491889 139718201411923184020118917)
  ·
    refine ⟨26197162764735597003772297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139718201411923184020118917 26197162764735597003772297)
    ·
      refine ⟨19647872073551697752829223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26197162764735597003772297 19647872073551697752829223)
      ·
        refine ⟨29471808110327546629243835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19647872073551697752829223 29471808110327546629243835)
        ·
          refine ⟨44207712165491319943865753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29471808110327546629243835 44207712165491319943865753)
          ·
            refine ⟨33155784124118489957899315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44207712165491319943865753 33155784124118489957899315)
            ·
              refine ⟨49733676186177734936848973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33155784124118489957899315 49733676186177734936848973)
              ·
                refine ⟨18650128569816650601318365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49733676186177734936848973 18650128569816650601318365)
                ·
                  refine ⟨6993798213681243975494387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18650128569816650601318365 6993798213681243975494387)
                  ·
                    refine ⟨10490697320521865963241581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6993798213681243975494387 10490697320521865963241581)
                    ·
                      refine ⟨3934011495195699736215593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10490697320521865963241581 3934011495195699736215593)
                      ·
                        rfl

theorem cell23_7661460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_7661460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661460 prefixEnd_7661460 := by exact prefixLift 7661460
  have htrace : WordTrace (prefixWord ++ tailWord_7661460) baseStart_7661460 baseEnd_7661460 := by
    simpa [prefixWord, tailWord_7661460, baseEnd_7661460] using wordTrace_append hprefix tailTrace_7661460
  have hstable : (prefixWord ++ tailWord_7661460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661460).length < 2 ^ (prefixWord ++ tailWord_7661460).sum := by decide
  have hdescent : baseEnd_7661460 < baseStart_7661460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661493 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 4, 4]
def baseStart_7661493 : Nat := 118140960795 + 7661493 * 2 ^ 59
def prefixEnd_7661493 : Nat := 4983230072969 + 3 ^ 40 * 7661493 * 2
def baseEnd_7661493 : Nat := 1311342813352432702367647

theorem tailTrace_7661493 : CollatzResearch.WordTrace tailWord_7661493 prefixEnd_7661493 1311342813352432702367647 := by
  unfold tailWord_7661493
  simp only [CollatzResearch.WordTrace]
  refine ⟨279437606432726814676189133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186291737621817876450792755 279437606432726814676189133)
  ·
    refine ⟨104789102412272555503570925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279437606432726814676189133 104789102412272555503570925)
    ·
      refine ⟨39295913404602208313839097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104789102412272555503570925 39295913404602208313839097)
      ·
        refine ⟨29471935053451656235379323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39295913404602208313839097 29471935053451656235379323)
        ·
          refine ⟨44207902580177484353068985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29471935053451656235379323 44207902580177484353068985)
          ·
            refine ⟨33155926935133113264801739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44207902580177484353068985 33155926935133113264801739)
            ·
              refine ⟨49733890402699669897202609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33155926935133113264801739 49733890402699669897202609)
              ·
                refine ⟨37300417802024752422901957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49733890402699669897202609 37300417802024752422901957)
                ·
                  refine ⟨6993828337879641079294117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37300417802024752422901957 6993828337879641079294117)
                  ·
                    refine ⟨1311342813352432702367647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6993828337879641079294117 1311342813352432702367647)
                    ·
                      rfl

theorem cell23_7661493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_7661493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661493 prefixEnd_7661493 := by exact prefixLift 7661493
  have htrace : WordTrace (prefixWord ++ tailWord_7661493) baseStart_7661493 baseEnd_7661493 := by
    simpa [prefixWord, tailWord_7661493, baseEnd_7661493] using wordTrace_append hprefix tailTrace_7661493
  have hstable : (prefixWord ++ tailWord_7661493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661493).length < 2 ^ (prefixWord ++ tailWord_7661493).sum := by decide
  have hdescent : baseEnd_7661493 < baseStart_7661493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661496 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 3, 2, 4]
def baseStart_7661496 : Nat := 118140960795 + 7661496 * 2 ^ 59
def prefixEnd_7661496 : Nat := 4983230072969 + 3 ^ 40 * 7661496 * 2
def baseEnd_7661496 : Nat := 3934029980499261595365427

theorem tailTrace_7661496 : CollatzResearch.WordTrace tailWord_7661496 prefixEnd_7661496 3934029980499261595365427 := by
  unfold tailWord_7661496
  simp only [CollatzResearch.WordTrace]
  refine ⟨139718857925857973094274171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186291810567810630792365561 139718857925857973094274171)
  ·
    refine ⟨209578286888786959641411257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139718857925857973094274171 209578286888786959641411257)
    ·
      refine ⟨157183715166590219731058443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209578286888786959641411257 157183715166590219731058443)
      ·
        refine ⟨235775572749885329596587665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157183715166590219731058443 235775572749885329596587665)
        ·
          refine ⟨176831679562413997197440749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235775572749885329596587665 176831679562413997197440749)
          ·
            refine ⟨66311879835905248949040281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176831679562413997197440749 66311879835905248949040281)
            ·
              refine ⟨49733909876928936711780211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66311879835905248949040281 49733909876928936711780211)
              ·
                refine ⟨74600864815393405067670317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49733909876928936711780211 74600864815393405067670317)
                ·
                  refine ⟨27975324305772526900376369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74600864815393405067670317 27975324305772526900376369)
                  ·
                    refine ⟨20981493229329395175282277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27975324305772526900376369 20981493229329395175282277)
                    ·
                      refine ⟨3934029980499261595365427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20981493229329395175282277 3934029980499261595365427)
                      ·
                        rfl

theorem cell23_7661496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_7661496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661496 prefixEnd_7661496 := by exact prefixLift 7661496
  have htrace : WordTrace (prefixWord ++ tailWord_7661496) baseStart_7661496 baseEnd_7661496 := by
    simpa [prefixWord, tailWord_7661496, baseEnd_7661496] using wordTrace_append hprefix tailTrace_7661496
  have hstable : (prefixWord ++ tailWord_7661496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661496).length < 2 ^ (prefixWord ++ tailWord_7661496).sum := by decide
  have hdescent : baseEnd_7661496 < baseStart_7661496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661503 : List Nat := [1, 1, 2, 2, 2, 1, 3, 5, 1, 2, 3]
def baseStart_7661503 : Nat := 118140960795 + 7661503 * 2 ^ 59
def prefixEnd_7661503 : Nat := 4983230072969 + 3 ^ 40 * 7661503 * 2
def baseEnd_7661503 : Nat := 3934033574863843067977895

theorem tailTrace_7661503 : CollatzResearch.WordTrace tailWord_7661503 prefixEnd_7661503 3934033574863843067977895 := by
  unfold tailWord_7661503
  simp only [CollatzResearch.WordTrace]
  refine ⟨279437971162690586384053163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186291980775127057589368775 279437971162690586384053163)
  ·
    refine ⟨419156956744035879576079745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279437971162690586384053163 419156956744035879576079745)
    ·
      refine ⟨314367717558026909682059809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419156956744035879576079745 314367717558026909682059809)
      ·
        refine ⟨235775788168520182261544857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314367717558026909682059809 235775788168520182261544857)
        ·
          refine ⟨176831841126390136696158643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235775788168520182261544857 176831841126390136696158643)
          ·
            refine ⟨265247761689585205044237965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176831841126390136696158643 265247761689585205044237965)
            ·
              refine ⟨99467910633594451891589237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265247761689585205044237965 99467910633594451891589237)
              ·
                refine ⟨9325116621899479864836491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99467910633594451891589237 9325116621899479864836491)
                ·
                  refine ⟨13987674932849219797254737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9325116621899479864836491 13987674932849219797254737)
                  ·
                    refine ⟨10490756199636914847941053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13987674932849219797254737 10490756199636914847941053)
                    ·
                      refine ⟨3934033574863843067977895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10490756199636914847941053 3934033574863843067977895)
                      ·
                        rfl

theorem cell23_7661503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 2, 3].length) (baseStart_7661503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661503 prefixEnd_7661503 := by exact prefixLift 7661503
  have htrace : WordTrace (prefixWord ++ tailWord_7661503) baseStart_7661503 baseEnd_7661503 := by
    simpa [prefixWord, tailWord_7661503, baseEnd_7661503] using wordTrace_append hprefix tailTrace_7661503
  have hstable : (prefixWord ++ tailWord_7661503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661503).length < 2 ^ (prefixWord ++ tailWord_7661503).sum := by decide
  have hdescent : baseEnd_7661503 < baseStart_7661503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661550 : List Nat := [4, 1, 2, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_7661550 : Nat := 118140960795 + 7661550 * 2 ^ 59
def prefixEnd_7661550 : Nat := 4983230072969 + 3 ^ 40 * 7661550 * 2
def baseEnd_7661550 : Nat := 3934057708454604384090179

theorem tailTrace_7661550 : CollatzResearch.WordTrace tailWord_7661550 prefixEnd_7661550 3934057708454604384090179 := by
  unfold tailWord_7661550
  simp only [CollatzResearch.WordTrace]
  refine ⟨34929960674190039176376763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186293123595680208940676069 34929960674190039176376763)
  ·
    refine ⟨52394941011285058764565145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34929960674190039176376763 52394941011285058764565145)
    ·
      refine ⟨39296205758463794073423859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52394941011285058764565145 39296205758463794073423859)
      ·
        refine ⟨58944308637695691110135789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39296205758463794073423859 58944308637695691110135789)
        ·
          refine ⟨22104115739135884166300921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58944308637695691110135789 22104115739135884166300921)
          ·
            refine ⟨16578086804351913124725691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22104115739135884166300921 16578086804351913124725691)
            ·
              refine ⟨24867130206527869687088537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16578086804351913124725691 24867130206527869687088537)
              ·
                refine ⟨18650347654895902265316403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24867130206527869687088537 18650347654895902265316403)
                ·
                  refine ⟨27975521482343853397974605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18650347654895902265316403 27975521482343853397974605)
                  ·
                    refine ⟨10490820555878945024240477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27975521482343853397974605 10490820555878945024240477)
                    ·
                      refine ⟨3934057708454604384090179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10490820555878945024240477 3934057708454604384090179)
                      ·
                        rfl

theorem cell23_7661550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_7661550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661550 prefixEnd_7661550 := by exact prefixLift 7661550
  have htrace : WordTrace (prefixWord ++ tailWord_7661550) baseStart_7661550 baseEnd_7661550 := by
    simpa [prefixWord, tailWord_7661550, baseEnd_7661550] using wordTrace_append hprefix tailTrace_7661550
  have hstable : (prefixWord ++ tailWord_7661550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661550).length < 2 ^ (prefixWord ++ tailWord_7661550).sum := by decide
  have hdescent : baseEnd_7661550 < baseStart_7661550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661560 : List Nat := [2, 1, 2, 1, 1, 3, 2, 5, 1, 3, 2]
def baseStart_7661560 : Nat := 118140960795 + 7661560 * 2 ^ 59
def prefixEnd_7661560 : Nat := 4983230072969 + 3 ^ 40 * 7661560 * 2
def baseEnd_7661560 : Nat := 3934062843261149344965133

theorem tailTrace_7661560 : CollatzResearch.WordTrace tailWord_7661560 prefixEnd_7661560 3934062843261149344965133 := by
  unfold tailWord_7661560
  simp only [CollatzResearch.WordTrace]
  refine ⟨139720025061742042559439067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186293366748989390079252089 139720025061742042559439067)
  ·
    refine ⟨209580037592613063839158601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139720025061742042559439067 209580037592613063839158601)
    ·
      refine ⟨157185028194459797879368951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209580037592613063839158601 157185028194459797879368951)
      ·
        refine ⟨235777542291689696819053427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157185028194459797879368951 235777542291689696819053427)
        ·
          refine ⟨353666313437534545228580141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235777542291689696819053427 353666313437534545228580141)
          ·
            refine ⟨132624867539075454460717553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353666313437534545228580141 132624867539075454460717553)
            ·
              refine ⟨99468650654306590845538165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132624867539075454460717553 99468650654306590845538165)
              ·
                refine ⟨9325185998841242891769203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99468650654306590845538165 9325185998841242891769203)
                ·
                  refine ⟨13987778998261864337653805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9325185998841242891769203 13987778998261864337653805)
                  ·
                    refine ⟨5245417124348199126620177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13987778998261864337653805 5245417124348199126620177)
                    ·
                      refine ⟨3934062843261149344965133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245417124348199126620177 3934062843261149344965133)
                      ·
                        rfl

theorem cell23_7661560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 1, 3, 2].length) (baseStart_7661560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661560 prefixEnd_7661560 := by exact prefixLift 7661560
  have htrace : WordTrace (prefixWord ++ tailWord_7661560) baseStart_7661560 baseEnd_7661560 := by
    simpa [prefixWord, tailWord_7661560, baseEnd_7661560] using wordTrace_append hprefix tailTrace_7661560
  have hstable : (prefixWord ++ tailWord_7661560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661560).length < 2 ^ (prefixWord ++ tailWord_7661560).sum := by decide
  have hdescent : baseEnd_7661560 < baseStart_7661560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661623 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 3]
def baseStart_7661623 : Nat := 118140960795 + 7661623 * 2 ^ 59
def prefixEnd_7661623 : Nat := 4983230072969 + 3 ^ 40 * 7661623 * 2
def baseEnd_7661623 : Nat := 3934095192542382598477343

theorem tailTrace_7661623 : CollatzResearch.WordTrace tailWord_7661623 prefixEnd_7661623 3934095192542382598477343 := by
  unfold tailWord_7661623
  simp only [CollatzResearch.WordTrace]
  refine ⟨279442347922255846878421523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186294898614837231252281015 279442347922255846878421523)
  ·
    refine ⟨419163521883383770317632285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279442347922255846878421523 419163521883383770317632285)
    ·
      refine ⟨157186320706268913869112107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419163521883383770317632285 157186320706268913869112107)
      ·
        refine ⟨235779481059403370803668161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157186320706268913869112107 235779481059403370803668161)
        ·
          refine ⟨176834610794552528102751121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235779481059403370803668161 176834610794552528102751121)
          ·
            refine ⟨132625958095914396077063341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176834610794552528102751121 132625958095914396077063341)
            ·
              refine ⟨49734734285967898528898753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132625958095914396077063341 49734734285967898528898753)
              ·
                refine ⟨37301050714475923896674065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49734734285967898528898753 37301050714475923896674065)
                ·
                  refine ⟨27975788035856942922505549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37301050714475923896674065 27975788035856942922505549)
                  ·
                    refine ⟨10490920513446353595939581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27975788035856942922505549 10490920513446353595939581)
                    ·
                      refine ⟨3934095192542382598477343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10490920513446353595939581 3934095192542382598477343)
                      ·
                        rfl

theorem cell23_7661623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_7661623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661623 prefixEnd_7661623 := by exact prefixLift 7661623
  have htrace : WordTrace (prefixWord ++ tailWord_7661623) baseStart_7661623 baseEnd_7661623 := by
    simpa [prefixWord, tailWord_7661623, baseEnd_7661623] using wordTrace_append hprefix tailTrace_7661623
  have hstable : (prefixWord ++ tailWord_7661623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661623).length < 2 ^ (prefixWord ++ tailWord_7661623).sum := by decide
  have hdescent : baseEnd_7661623 < baseStart_7661623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661680 : List Nat := [2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 4]
def baseStart_7661680 : Nat := 118140960795 + 7661680 * 2 ^ 59
def prefixEnd_7661680 : Nat := 4983230072969 + 3 ^ 40 * 7661680 * 2
def baseEnd_7661680 : Nat := 3934124460939688875464581

theorem tailTrace_7661680 : CollatzResearch.WordTrace tailWord_7661680 prefixEnd_7661680 3934124460939688875464581 := by
  unfold tailWord_7661680
  simp only [CollatzResearch.WordTrace]
  refine ⟨139722213441524672806623247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186296284588699563742164329 139722213441524672806623247)
  ·
    refine ⟨209583320162287009209934871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139722213441524672806623247 209583320162287009209934871)
    ·
      refine ⟨314374980243430513814902307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209583320162287009209934871 314374980243430513814902307)
      ·
        refine ⟨471562470365145770722353461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314374980243430513814902307 471562470365145770722353461)
        ·
          refine ⟨44208981596732416005220637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 471562470365145770722353461 44208981596732416005220637)
          ·
            refine ⟨16578368098774656001957739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44208981596732416005220637 16578368098774656001957739)
            ·
              refine ⟨24867552148161984002936609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16578368098774656001957739 24867552148161984002936609)
              ·
                refine ⟨18650664111121488002202457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24867552148161984002936609 18650664111121488002202457)
                ·
                  refine ⟨13987998083341116001651843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18650664111121488002202457 13987998083341116001651843)
                  ·
                    refine ⟨20981997125011674002477765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13987998083341116001651843 20981997125011674002477765)
                    ·
                      refine ⟨3934124460939688875464581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20981997125011674002477765 3934124460939688875464581)
                      ·
                        rfl

theorem cell23_7661680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 4].length) (baseStart_7661680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661680 prefixEnd_7661680 := by exact prefixLift 7661680
  have htrace : WordTrace (prefixWord ++ tailWord_7661680) baseStart_7661680 baseEnd_7661680 := by
    simpa [prefixWord, tailWord_7661680, baseEnd_7661680] using wordTrace_append hprefix tailTrace_7661680
  have hstable : (prefixWord ++ tailWord_7661680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661680).length < 2 ^ (prefixWord ++ tailWord_7661680).sum := by decide
  have hdescent : baseEnd_7661680 < baseStart_7661680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661700 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_7661700 : Nat := 118140960795 + 7661700 * 2 ^ 59
def prefixEnd_7661700 : Nat := 4983230072969 + 3 ^ 40 * 7661700 * 2
def baseEnd_7661700 : Nat := 3934134730552778797214489

theorem tailTrace_7661700 : CollatzResearch.WordTrace tailWord_7661700 prefixEnd_7661700 3934134730552778797214489 := by
  unfold tailWord_7661700
  simp only [CollatzResearch.WordTrace]
  refine ⟨139722578171488444514487277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186296770895317926019316369 139722578171488444514487277)
  ·
    refine ⟨52395966814308166692932729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139722578171488444514487277 52395966814308166692932729)
    ·
      refine ⟨39296975110731125019699547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52395966814308166692932729 39296975110731125019699547)
      ·
        refine ⟨58945462666096687529549321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39296975110731125019699547 58945462666096687529549321)
        ·
          refine ⟨44209096999572515647161991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58945462666096687529549321 44209096999572515647161991)
          ·
            refine ⟨66313645499358773470742987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44209096999572515647161991 66313645499358773470742987)
            ·
              refine ⟨99470468249038160206114481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66313645499358773470742987 99470468249038160206114481)
              ·
                refine ⟨74602851186778620154585861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99470468249038160206114481 74602851186778620154585861)
                ·
                  refine ⟨13988034597520991278984849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74602851186778620154585861 13988034597520991278984849)
                  ·
                    refine ⟨10491025948140743459238637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13988034597520991278984849 10491025948140743459238637)
                    ·
                      refine ⟨3934134730552778797214489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10491025948140743459238637 3934134730552778797214489)
                      ·
                        rfl

theorem cell23_7661700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_7661700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661700 prefixEnd_7661700 := by exact prefixLift 7661700
  have htrace : WordTrace (prefixWord ++ tailWord_7661700) baseStart_7661700 baseEnd_7661700 := by
    simpa [prefixWord, tailWord_7661700, baseEnd_7661700] using wordTrace_append hprefix tailTrace_7661700
  have hstable : (prefixWord ++ tailWord_7661700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661700).length < 2 ^ (prefixWord ++ tailWord_7661700).sum := by decide
  have hdescent : baseEnd_7661700 < baseStart_7661700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661741 : List Nat := [1, 5, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_7661741 : Nat := 118140960795 + 7661741 * 2 ^ 59
def prefixEnd_7661741 : Nat := 4983230072969 + 3 ^ 40 * 7661741 * 2
def baseEnd_7661741 : Nat := 1311385261086537712267267

theorem tailTrace_7661741 : CollatzResearch.WordTrace tailWord_7661741 prefixEnd_7661741 1311385261086537712267267 := by
  unfold tailWord_7661741
  simp only [CollatzResearch.WordTrace]
  refine ⟨279446651735828353031217077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186297767823885568687478051 279446651735828353031217077)
  ·
    refine ⟨26198123600233908096676601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279446651735828353031217077 26198123600233908096676601)
    ·
      refine ⟨19648592700175431072507451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26198123600233908096676601 19648592700175431072507451)
      ·
        refine ⟨29472889050263146608761177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19648592700175431072507451 29472889050263146608761177)
        ·
          refine ⟨22104666787697359956570883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29472889050263146608761177 22104666787697359956570883)
          ·
            refine ⟨33157000181546039934856325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22104666787697359956570883 33157000181546039934856325)
            ·
              refine ⟨6216937534039882487785561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33157000181546039934856325 6216937534039882487785561)
              ·
                refine ⟨4662703150529911865839171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6216937534039882487785561 4662703150529911865839171)
                ·
                  refine ⟨6994054725794867798758757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4662703150529911865839171 6994054725794867798758757)
                  ·
                    refine ⟨1311385261086537712267267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6994054725794867798758757 1311385261086537712267267)
                    ·
                      rfl

theorem cell23_7661741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_7661741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661741 prefixEnd_7661741 := by exact prefixLift 7661741
  have htrace : WordTrace (prefixWord ++ tailWord_7661741) baseStart_7661741 baseEnd_7661741 := by
    simpa [prefixWord, tailWord_7661741, baseEnd_7661741] using wordTrace_append hprefix tailTrace_7661741
  have hstable : (prefixWord ++ tailWord_7661741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661741).length < 2 ^ (prefixWord ++ tailWord_7661741).sum := by decide
  have hdescent : baseEnd_7661741 < baseStart_7661741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661748 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_7661748 : Nat := 118140960795 + 7661748 * 2 ^ 59
def prefixEnd_7661748 : Nat := 4983230072969 + 3 ^ 40 * 7661748 * 2
def baseEnd_7661748 : Nat := 3934159377624194609414269

theorem tailTrace_7661748 : CollatzResearch.WordTrace tailWord_7661748 prefixEnd_7661748 3934159377624194609414269 := by
  unfold tailWord_7661748
  simp only [CollatzResearch.WordTrace]
  refine ⟨139723453523401496613360949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186297938031201995484481265 139723453523401496613360949)
  ·
    refine ⟨13099073767818890307502589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139723453523401496613360949 13099073767818890307502589)
    ·
      refine ⟨4912152662932083865313471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13099073767818890307502589 4912152662932083865313471)
      ·
        refine ⟨7368228994398125797970207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4912152662932083865313471 7368228994398125797970207)
        ·
          refine ⟨11052343491597188696955311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7368228994398125797970207 11052343491597188696955311)
          ·
            refine ⟨16578515237395783045432967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11052343491597188696955311 16578515237395783045432967)
            ·
              refine ⟨24867772856093674568149451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16578515237395783045432967 24867772856093674568149451)
              ·
                refine ⟨37301659284140511852224177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24867772856093674568149451 37301659284140511852224177)
                ·
                  refine ⟨27976244463105383889168133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37301659284140511852224177 27976244463105383889168133)
                  ·
                    refine ⟨5245545836832259479219025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27976244463105383889168133 5245545836832259479219025)
                    ·
                      refine ⟨3934159377624194609414269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245545836832259479219025 3934159377624194609414269)
                      ·
                        rfl

theorem cell23_7661748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_7661748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661748 prefixEnd_7661748 := by exact prefixLift 7661748
  have htrace : WordTrace (prefixWord ++ tailWord_7661748) baseStart_7661748 baseEnd_7661748 := by
    simpa [prefixWord, tailWord_7661748, baseEnd_7661748] using wordTrace_append hprefix tailTrace_7661748
  have hstable : (prefixWord ++ tailWord_7661748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661748).length < 2 ^ (prefixWord ++ tailWord_7661748).sum := by decide
  have hdescent : baseEnd_7661748 < baseStart_7661748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661764 : List Nat := [2, 3, 3, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_7661764 : Nat := 118140960795 + 7661764 * 2 ^ 59
def prefixEnd_7661764 : Nat := 4983230072969 + 3 ^ 40 * 7661764 * 2
def baseEnd_7661764 : Nat := 3934167593314666546814195

theorem tailTrace_7661764 : CollatzResearch.WordTrace tailWord_7661764 prefixEnd_7661764 3934167593314666546814195 := by
  unfold tailWord_7661764
  simp only [CollatzResearch.WordTrace]
  refine ⟨139723745307372513979652173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186298327076496685306202897 139723745307372513979652173)
  ·
    refine ⟨52396404490264692742369565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139723745307372513979652173 52396404490264692742369565)
    ·
      refine ⟨19648651683849259778388587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52396404490264692742369565 19648651683849259778388587)
      ·
        refine ⟨29472977525773889667582881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19648651683849259778388587 29472977525773889667582881)
        ·
          refine ⟨22104733144330417250687161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29472977525773889667582881 22104733144330417250687161)
          ·
            refine ⟨16578549858247812938015371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22104733144330417250687161 16578549858247812938015371)
            ·
              refine ⟨24867824787371719407023057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16578549858247812938015371 24867824787371719407023057)
              ·
                refine ⟨18650868590528789555267293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24867824787371719407023057 18650868590528789555267293)
                ·
                  refine ⟨6994075721448296083225235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18650868590528789555267293 6994075721448296083225235)
                  ·
                    refine ⟨10491113582172444124837853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6994075721448296083225235 10491113582172444124837853)
                    ·
                      refine ⟨3934167593314666546814195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10491113582172444124837853 3934167593314666546814195)
                      ·
                        rfl

theorem cell23_7661764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_7661764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661764 prefixEnd_7661764 := by exact prefixLift 7661764
  have htrace : WordTrace (prefixWord ++ tailWord_7661764) baseStart_7661764 baseEnd_7661764 := by
    simpa [prefixWord, tailWord_7661764, baseEnd_7661764] using wordTrace_append hprefix tailTrace_7661764
  have hstable : (prefixWord ++ tailWord_7661764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661764).length < 2 ^ (prefixWord ++ tailWord_7661764).sum := by decide
  have hdescent : baseEnd_7661764 < baseStart_7661764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661770 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_7661770 : Nat := 118140960795 + 7661770 * 2 ^ 59
def prefixEnd_7661770 : Nat := 4983230072969 + 3 ^ 40 * 7661770 * 2
def baseEnd_7661770 : Nat := 3934170674198593523339167

theorem tailTrace_7661770 : CollatzResearch.WordTrace tailWord_7661770 prefixEnd_7661770 3934170674198593523339167 := by
  unfold tailWord_7661770
  simp only [CollatzResearch.WordTrace]
  refine ⟨69861927363180822746005691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186298472968482193989348509 69861927363180822746005691)
  ·
    refine ⟨104792891044771234119008537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69861927363180822746005691 104792891044771234119008537)
    ·
      refine ⟨78594668283578425589256403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104792891044771234119008537 78594668283578425589256403)
      ·
        refine ⟨117892002425367638383884605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78594668283578425589256403 117892002425367638383884605)
        ·
          refine ⟨44209500909512864393956727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117892002425367638383884605 44209500909512864393956727)
          ·
            refine ⟨66314251364269296590935091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44209500909512864393956727 66314251364269296590935091)
            ·
              refine ⟨99471377046403944886402637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66314251364269296590935091 99471377046403944886402637)
              ·
                refine ⟨37301766392401479332400989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99471377046403944886402637 37301766392401479332400989)
                ·
                  refine ⟨13988162397150554749650371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37301766392401479332400989 13988162397150554749650371)
                  ·
                    refine ⟨20982243595725832124475557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13988162397150554749650371 20982243595725832124475557)
                    ·
                      refine ⟨3934170674198593523339167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20982243595725832124475557 3934170674198593523339167)
                      ·
                        rfl

theorem cell23_7661770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_7661770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661770 prefixEnd_7661770 := by exact prefixLift 7661770
  have htrace : WordTrace (prefixWord ++ tailWord_7661770) baseStart_7661770 baseEnd_7661770 := by
    simpa [prefixWord, tailWord_7661770, baseEnd_7661770] using wordTrace_append hprefix tailTrace_7661770
  have hstable : (prefixWord ++ tailWord_7661770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661770).length < 2 ^ (prefixWord ++ tailWord_7661770).sum := by decide
  have hdescent : baseEnd_7661770 < baseStart_7661770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661774 : List Nat := [4, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2]
def baseStart_7661774 : Nat := 118140960795 + 7661774 * 2 ^ 59
def prefixEnd_7661774 : Nat := 4983230072969 + 3 ^ 40 * 7661774 * 2
def baseEnd_7661774 : Nat := 3934172728121211507689149

theorem tailTrace_7661774 : CollatzResearch.WordTrace tailWord_7661774 prefixEnd_7661774 3934172728121211507689149 := by
  unfold tailWord_7661774
  simp only [CollatzResearch.WordTrace]
  refine ⟨34930981918088599958396047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186298570229805866444778917 34930981918088599958396047)
  ·
    refine ⟨52396472877132899937594071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34930981918088599958396047 52396472877132899937594071)
    ·
      refine ⟨78594709315699349906391107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52396472877132899937594071 78594709315699349906391107)
      ·
        refine ⟨117892063973549024859586661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78594709315699349906391107 117892063973549024859586661)
        ·
          refine ⟨22104761995040442161172499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117892063973549024859586661 22104761995040442161172499)
          ·
            refine ⟨33157142992560663241758749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22104761995040442161172499 33157142992560663241758749)
            ·
              refine ⟨12433928622210248715659531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33157142992560663241758749 12433928622210248715659531)
              ·
                refine ⟨18650892933315373073489297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12433928622210248715659531 18650892933315373073489297)
                ·
                  refine ⟨13988169699986529805116973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18650892933315373073489297 13988169699986529805116973)
                  ·
                    refine ⟨5245563637494948676918865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13988169699986529805116973 5245563637494948676918865)
                    ·
                      refine ⟨3934172728121211507689149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245563637494948676918865 3934172728121211507689149)
                      ·
                        rfl

theorem cell23_7661774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_7661774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661774 prefixEnd_7661774 := by exact prefixLift 7661774
  have htrace : WordTrace (prefixWord ++ tailWord_7661774) baseStart_7661774 baseEnd_7661774 := by
    simpa [prefixWord, tailWord_7661774, baseEnd_7661774] using wordTrace_append hprefix tailTrace_7661774
  have hstable : (prefixWord ++ tailWord_7661774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661774).length < 2 ^ (prefixWord ++ tailWord_7661774).sum := by decide
  have hdescent : baseEnd_7661774 < baseStart_7661774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661783 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 6]
def baseStart_7661783 : Nat := 118140960795 + 7661783 * 2 ^ 59
def prefixEnd_7661783 : Nat := 4983230072969 + 3 ^ 40 * 7661783 * 2
def baseEnd_7661783 : Nat := 3934177349447101972476607

theorem tailTrace_7661783 : CollatzResearch.WordTrace tailWord_7661783 prefixEnd_7661783 3934177349447101972476607 := by
  unfold tailWord_7661783
  simp only [CollatzResearch.WordTrace]
  refine ⟨279448183601676194204246003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186298789067784129469497335 279448183601676194204246003)
  ·
    refine ⟨419172275402514291306369005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279448183601676194204246003 419172275402514291306369005)
    ·
      refine ⟨157189603275942859239888377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419172275402514291306369005 157189603275942859239888377)
      ·
        refine ⟨117892202456957144429916283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157189603275942859239888377 117892202456957144429916283)
        ·
          refine ⟨176838303685435716644874425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117892202456957144429916283 176838303685435716644874425)
          ·
            refine ⟨132628727764076787483655819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176838303685435716644874425 132628727764076787483655819)
            ·
              refine ⟨198943091646115181225483729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132628727764076787483655819 198943091646115181225483729)
              ·
                refine ⟨149207318734586385919112797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198943091646115181225483729 149207318734586385919112797)
                ·
                  refine ⟨55952744525469894719667299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149207318734586385919112797 55952744525469894719667299)
                  ·
                    refine ⟨83929116788204842079500949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55952744525469894719667299 83929116788204842079500949)
                    ·
                      refine ⟨3934177349447101972476607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83929116788204842079500949 3934177349447101972476607)
                      ·
                        rfl

theorem cell23_7661783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_7661783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661783 prefixEnd_7661783 := by exact prefixLift 7661783
  have htrace : WordTrace (prefixWord ++ tailWord_7661783) baseStart_7661783 baseEnd_7661783 := by
    simpa [prefixWord, tailWord_7661783, baseEnd_7661783] using wordTrace_append hprefix tailTrace_7661783
  have hstable : (prefixWord ++ tailWord_7661783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661783).length < 2 ^ (prefixWord ++ tailWord_7661783).sum := by decide
  have hdescent : baseEnd_7661783 < baseStart_7661783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661784 : List Nat := [2, 1, 2, 2, 4, 3, 2, 1, 1, 5]
def baseStart_7661784 : Nat := 118140960795 + 7661784 * 2 ^ 59
def prefixEnd_7661784 : Nat := 4983230072969 + 3 ^ 40 * 7661784 * 2
def baseEnd_7661784 : Nat := 1311392620975918822854701

theorem tailTrace_7661784 : CollatzResearch.WordTrace tailWord_7661784 prefixEnd_7661784 1311392620975918822854701 := by
  unfold tailWord_7661784
  simp only [CollatzResearch.WordTrace]
  refine ⟨139724110037336285687516203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186298813383115047583354937 139724110037336285687516203)
  ·
    refine ⟨209586165056004428531274305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139724110037336285687516203 209586165056004428531274305)
    ·
      refine ⟨157189623792003321398455729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209586165056004428531274305 157189623792003321398455729)
      ·
        refine ⟨117892217844002491048841797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157189623792003321398455729 117892217844002491048841797)
        ·
          refine ⟨22104790845750467071657837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117892217844002491048841797 22104790845750467071657837)
          ·
            refine ⟨8289296567156425151871689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22104790845750467071657837 8289296567156425151871689)
            ·
              refine ⟨6216972425367318863903767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8289296567156425151871689 6216972425367318863903767)
              ·
                refine ⟨9325458638050978295855651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6216972425367318863903767 9325458638050978295855651)
                ·
                  refine ⟨13988187957076467443783477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9325458638050978295855651 13988187957076467443783477)
                  ·
                    refine ⟨1311392620975918822854701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13988187957076467443783477 1311392620975918822854701)
                    ·
                      rfl

theorem cell23_7661784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 1, 5].length) (baseStart_7661784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661784 prefixEnd_7661784 := by exact prefixLift 7661784
  have htrace : WordTrace (prefixWord ++ tailWord_7661784) baseStart_7661784 baseEnd_7661784 := by
    simpa [prefixWord, tailWord_7661784, baseEnd_7661784] using wordTrace_append hprefix tailTrace_7661784
  have hstable : (prefixWord ++ tailWord_7661784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661784).length < 2 ^ (prefixWord ++ tailWord_7661784).sum := by decide
  have hdescent : baseEnd_7661784 < baseStart_7661784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661793 : List Nat := [1, 2, 3, 1, 3, 1, 12]
def baseStart_7661793 : Nat := 118140960795 + 7661793 * 2 ^ 59
def prefixEnd_7661793 : Nat := 4983230072969 + 3 ^ 40 * 7661793 * 2
def baseEnd_7661793 : Nat := 48570154126588233745081

theorem tailTrace_7661793 : CollatzResearch.WordTrace tailWord_7661793 prefixEnd_7661793 48570154126588233745081 := by
  unfold tailWord_7661793
  simp only [CollatzResearch.WordTrace]
  refine ⟨279448548331639965912110033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186299032221093310608073355 279448548331639965912110033)
  ·
    refine ⟨209586411248729974434082525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279448548331639965912110033 209586411248729974434082525)
    ·
      refine ⟨78594904218273740412780947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209586411248729974434082525 78594904218273740412780947)
      ·
        refine ⟨117892356327410610619171421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78594904218273740412780947 117892356327410610619171421)
        ·
          refine ⟨44209633622778978982189283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117892356327410610619171421 44209633622778978982189283)
          ·
            refine ⟨66314450434168468473283925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44209633622778978982189283 66314450434168468473283925)
            ·
              refine ⟨48570154126588233745081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 66314450434168468473283925 48570154126588233745081)
              ·
                rfl

theorem cell23_7661793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 12].length) (baseStart_7661793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661793 prefixEnd_7661793 := by exact prefixLift 7661793
  have htrace : WordTrace (prefixWord ++ tailWord_7661793) baseStart_7661793 baseEnd_7661793 := by
    simpa [prefixWord, tailWord_7661793, baseEnd_7661793] using wordTrace_append hprefix tailTrace_7661793
  have hstable : (prefixWord ++ tailWord_7661793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661793).length < 2 ^ (prefixWord ++ tailWord_7661793).sum := by decide
  have hdescent : baseEnd_7661793 < baseStart_7661793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661797 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 4, 4]
def baseStart_7661797 : Nat := 118140960795 + 7661797 * 2 ^ 59
def prefixEnd_7661797 : Nat := 4983230072969 + 3 ^ 40 * 7661797 * 2
def baseEnd_7661797 : Nat := 1311394846058754972567181

theorem tailTrace_7661797 : CollatzResearch.WordTrace tailWord_7661797 prefixEnd_7661797 1311394846058754972567181 := by
  unfold tailWord_7661797
  simp only [CollatzResearch.WordTrace]
  refine ⟨279448694223625474595255645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186299129482416983063503763 279448694223625474595255645)
  ·
    refine ⟨104793260333859552973220867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279448694223625474595255645 104793260333859552973220867)
    ·
      refine ⟨157189890500789329459831301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104793260333859552973220867 157189890500789329459831301)
      ·
        refine ⟨29473104468897999273718369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157189890500789329459831301 29473104468897999273718369)
        ·
          refine ⟨22104828351673499455288777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29473104468897999273718369 22104828351673499455288777)
          ·
            refine ⟨16578621263755124591466583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22104828351673499455288777 16578621263755124591466583)
            ·
              refine ⟨24867931895632686887199875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16578621263755124591466583 24867931895632686887199875)
              ·
                refine ⟨37301897843449030330799813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24867931895632686887199875 37301897843449030330799813)
                ·
                  refine ⟨6994105845646693187024965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37301897843449030330799813 6994105845646693187024965)
                  ·
                    refine ⟨1311394846058754972567181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6994105845646693187024965 1311394846058754972567181)
                    ·
                      rfl

theorem cell23_7661797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_7661797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661797 prefixEnd_7661797 := by exact prefixLift 7661797
  have htrace : WordTrace (prefixWord ++ tailWord_7661797) baseStart_7661797 baseEnd_7661797 := by
    simpa [prefixWord, tailWord_7661797, baseEnd_7661797] using wordTrace_append hprefix tailTrace_7661797
  have hstable : (prefixWord ++ tailWord_7661797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661797).length < 2 ^ (prefixWord ++ tailWord_7661797).sum := by decide
  have hdescent : baseEnd_7661797 < baseStart_7661797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661804 : List Nat := [2, 2, 1, 1, 2, 3, 4, 1, 3, 2, 2]
def baseStart_7661804 : Nat := 118140960795 + 7661804 * 2 ^ 59
def prefixEnd_7661804 : Nat := 4983230072969 + 3 ^ 40 * 7661804 * 2
def baseEnd_7661804 : Nat := 3934188132540846390314011

theorem tailTrace_7661804 : CollatzResearch.WordTrace tailWord_7661804 prefixEnd_7661804 3934188132540846390314011 := by
  unfold tailWord_7661804
  simp only [CollatzResearch.WordTrace]
  refine ⟨139724474767300057395380233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186299299689733409860506977 139724474767300057395380233)
  ·
    refine ⟨104793356075475043046535175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139724474767300057395380233 104793356075475043046535175)
    ·
      refine ⟨157190034113212564569802763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104793356075475043046535175 157190034113212564569802763)
      ·
        refine ⟨235785051169818846854704145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157190034113212564569802763 235785051169818846854704145)
        ·
          refine ⟨176838788377364135141028109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235785051169818846854704145 176838788377364135141028109)
          ·
            refine ⟨66314545641511550677885541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176838788377364135141028109 66314545641511550677885541)
            ·
              refine ⟨12433977307783415752103539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66314545641511550677885541 12433977307783415752103539)
              ·
                refine ⟨18650965961675123628155309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12433977307783415752103539 18650965961675123628155309)
                ·
                  refine ⟨6994112235628171360558241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18650965961675123628155309 6994112235628171360558241)
                  ·
                    refine ⟨5245584176721128520418681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6994112235628171360558241 5245584176721128520418681)
                    ·
                      refine ⟨3934188132540846390314011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245584176721128520418681 3934188132540846390314011)
                      ·
                        rfl

theorem cell23_7661804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 2, 2].length) (baseStart_7661804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661804 prefixEnd_7661804 := by exact prefixLift 7661804
  have htrace : WordTrace (prefixWord ++ tailWord_7661804) baseStart_7661804 baseEnd_7661804 := by
    simpa [prefixWord, tailWord_7661804, baseEnd_7661804] using wordTrace_append hprefix tailTrace_7661804
  have hstable : (prefixWord ++ tailWord_7661804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661804).length < 2 ^ (prefixWord ++ tailWord_7661804).sum := by decide
  have hdescent : baseEnd_7661804 < baseStart_7661804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661843 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 8]
def baseStart_7661843 : Nat := 118140960795 + 7661843 * 2 ^ 59
def prefixEnd_7661843 : Nat := 4983230072969 + 3 ^ 40 * 7661843 * 2
def baseEnd_7661843 : Nat := 3934208158286371737726331

theorem tailTrace_7661843 : CollatzResearch.WordTrace tailWord_7661843 prefixEnd_7661843 3934208158286371737726331 := by
  unfold tailWord_7661843
  simp only [CollatzResearch.WordTrace]
  refine ⟨279450371981458824451430183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186300247987639216300953455 279450371981458824451430183)
  ·
    refine ⟨419175557972188236677145275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279450371981458824451430183 419175557972188236677145275)
    ·
      refine ⟨628763336958282355015717913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419175557972188236677145275 628763336958282355015717913)
      ·
        refine ⟨471572502718711766261788435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628763336958282355015717913 471572502718711766261788435)
        ·
          refine ⟨707358754078067649392682653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471572502718711766261788435 707358754078067649392682653)
          ·
            refine ⟨265259532779275368522255995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 707358754078067649392682653 265259532779275368522255995)
            ·
              refine ⟨397889299168913052783383993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265259532779275368522255995 397889299168913052783383993)
              ·
                refine ⟨298416974376684789587537995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397889299168913052783383993 298416974376684789587537995)
                ·
                  refine ⟨447625461565027184381306993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298416974376684789587537995 447625461565027184381306993)
                  ·
                    refine ⟨335719096173770388285980245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 447625461565027184381306993 335719096173770388285980245)
                    ·
                      refine ⟨3934208158286371737726331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 335719096173770388285980245 3934208158286371737726331)
                      ·
                        rfl

theorem cell23_7661843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_7661843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661843 prefixEnd_7661843 := by exact prefixLift 7661843
  have htrace : WordTrace (prefixWord ++ tailWord_7661843) baseStart_7661843 baseEnd_7661843 := by
    simpa [prefixWord, tailWord_7661843, baseEnd_7661843] using wordTrace_append hprefix tailTrace_7661843
  have hstable : (prefixWord ++ tailWord_7661843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661843).length < 2 ^ (prefixWord ++ tailWord_7661843).sum := by decide
  have hdescent : baseEnd_7661843 < baseStart_7661843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661880 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 2, 1, 5]
def baseStart_7661880 : Nat := 118140960795 + 7661880 * 2 ^ 59
def prefixEnd_7661880 : Nat := 4983230072969 + 3 ^ 40 * 7661880 * 2
def baseEnd_7661880 : Nat := 3934227157070588092963661

theorem tailTrace_7661880 : CollatzResearch.WordTrace tailWord_7661880 prefixEnd_7661880 3934227157070588092963661 := by
  unfold tailWord_7661880
  simp only [CollatzResearch.WordTrace]
  refine ⟨139725860741162389885263547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186301147654883186513684729 139725860741162389885263547)
  ·
    refine ⟨209588791111743584827895321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139725860741162389885263547 209588791111743584827895321)
    ·
      refine ⟨157191593333807688620921491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209588791111743584827895321 157191593333807688620921491)
      ·
        refine ⟨235787390000711532931382237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157191593333807688620921491 235787390000711532931382237)
        ·
          refine ⟨88420271250266824849268339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235787390000711532931382237 88420271250266824849268339)
          ·
            refine ⟨132630406875400237273902509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88420271250266824849268339 132630406875400237273902509)
            ·
              refine ⟨49736402578275088977713441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132630406875400237273902509 49736402578275088977713441)
              ·
                refine ⟨37302301933706316733285081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49736402578275088977713441 37302301933706316733285081)
                ·
                  refine ⟨27976726450279737549963811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37302301933706316733285081 27976726450279737549963811)
                  ·
                    refine ⟨41965089675419606324945717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27976726450279737549963811 41965089675419606324945717)
                    ·
                      refine ⟨3934227157070588092963661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41965089675419606324945717 3934227157070588092963661)
                      ·
                        rfl

theorem cell23_7661880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_7661880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661880 prefixEnd_7661880 := by exact prefixLift 7661880
  have htrace : WordTrace (prefixWord ++ tailWord_7661880) baseStart_7661880 baseEnd_7661880 := by
    simpa [prefixWord, tailWord_7661880, baseEnd_7661880] using wordTrace_append hprefix tailTrace_7661880
  have hstable : (prefixWord ++ tailWord_7661880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661880).length < 2 ^ (prefixWord ++ tailWord_7661880).sum := by decide
  have hdescent : baseEnd_7661880 < baseStart_7661880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661881 : List Nat := [1, 2, 1, 6, 1, 1, 3, 2, 1, 3, 2]
def baseStart_7661881 : Nat := 118140960795 + 7661881 * 2 ^ 59
def prefixEnd_7661881 : Nat := 4983230072969 + 3 ^ 40 * 7661881 * 2
def baseEnd_7661881 : Nat := 3934227670551242589051157

theorem tailTrace_7661881 : CollatzResearch.WordTrace tailWord_7661881 prefixEnd_7661881 3934227670551242589051157 := by
  unfold tailWord_7661881
  simp only [CollatzResearch.WordTrace]
  refine ⟨279451757955321156941313497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186301171970214104627542331 279451757955321156941313497)
  ·
    refine ⟨209588818466490867705985123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279451757955321156941313497 209588818466490867705985123)
    ·
      refine ⟨314383227699736301558977685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209588818466490867705985123 314383227699736301558977685)
      ·
        refine ⟨14736713798425139135577079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 314383227699736301558977685 14736713798425139135577079)
        ·
          refine ⟨22105070697637708703365619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14736713798425139135577079 22105070697637708703365619)
          ·
            refine ⟨33157606046456563055048429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22105070697637708703365619 33157606046456563055048429)
            ·
              refine ⟨12434102267421211145643161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33157606046456563055048429 12434102267421211145643161)
              ·
                refine ⟨9325576700565908359232371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12434102267421211145643161 9325576700565908359232371)
                ·
                  refine ⟨13988365050848862538848557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9325576700565908359232371 13988365050848862538848557)
                  ·
                    refine ⟨5245636894068323452068209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13988365050848862538848557 5245636894068323452068209)
                    ·
                      refine ⟨3934227670551242589051157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245636894068323452068209 3934227670551242589051157)
                      ·
                        rfl

theorem cell23_7661881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_7661881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661881 prefixEnd_7661881 := by exact prefixLift 7661881
  have htrace : WordTrace (prefixWord ++ tailWord_7661881) baseStart_7661881 baseEnd_7661881 := by
    simpa [prefixWord, tailWord_7661881, baseEnd_7661881] using wordTrace_append hprefix tailTrace_7661881
  have hstable : (prefixWord ++ tailWord_7661881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661881).length < 2 ^ (prefixWord ++ tailWord_7661881).sum := by decide
  have hdescent : baseEnd_7661881 < baseStart_7661881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661911 : List Nat := [1, 1, 3, 2, 3, 1, 4, 2, 2, 2, 2]
def baseStart_7661911 : Nat := 118140960795 + 7661911 * 2 ^ 59
def prefixEnd_7661911 : Nat := 4983230072969 + 3 ^ 40 * 7661911 * 2
def baseEnd_7661911 : Nat := 3934243074970877471676019

theorem tailTrace_7661911 : CollatzResearch.WordTrace tailWord_7661911 prefixEnd_7661911 3934243074970877471676019 := by
  unfold tailWord_7661911
  simp only [CollatzResearch.WordTrace]
  refine ⟨279452852145212472064905587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186301901430141648043270391 279452852145212472064905587)
  ·
    refine ⟨419179278217818708097358381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279452852145212472064905587 419179278217818708097358381)
    ·
      refine ⟨157192229331682015536509393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419179278217818708097358381 157192229331682015536509393)
      ·
        refine ⟨117894171998761511652382045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157192229331682015536509393 117894171998761511652382045)
        ·
          refine ⟨44210314499535566869643267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117894171998761511652382045 44210314499535566869643267)
          ·
            refine ⟨66315471749303350304464901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44210314499535566869643267 66315471749303350304464901)
            ·
              refine ⟨12434150952994378182087169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66315471749303350304464901 12434150952994378182087169)
              ·
                refine ⟨9325613214745783636565377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12434150952994378182087169 9325613214745783636565377)
                ·
                  refine ⟨6994209911059337727424033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9325613214745783636565377 6994209911059337727424033)
                  ·
                    refine ⟨5245657433294503295568025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6994209911059337727424033 5245657433294503295568025)
                    ·
                      refine ⟨3934243074970877471676019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245657433294503295568025 3934243074970877471676019)
                      ·
                        rfl

theorem cell23_7661911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_7661911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661911 prefixEnd_7661911 := by exact prefixLift 7661911
  have htrace : WordTrace (prefixWord ++ tailWord_7661911) baseStart_7661911 baseEnd_7661911 := by
    simpa [prefixWord, tailWord_7661911, baseEnd_7661911] using wordTrace_append hprefix tailTrace_7661911
  have hstable : (prefixWord ++ tailWord_7661911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661911).length < 2 ^ (prefixWord ++ tailWord_7661911).sum := by decide
  have hdescent : baseEnd_7661911 < baseStart_7661911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661927 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_7661927 : Nat := 118140960795 + 7661927 * 2 ^ 59
def prefixEnd_7661927 : Nat := 4983230072969 + 3 ^ 40 * 7661927 * 2
def baseEnd_7661927 : Nat := 3934251290661349409075945

theorem tailTrace_7661927 : CollatzResearch.WordTrace tailWord_7661927 prefixEnd_7661927 3934251290661349409075945 := by
  unfold tailWord_7661927
  simp only [CollatzResearch.WordTrace]
  refine ⟨279453435713154506797488035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186302290475436337864992023 279453435713154506797488035)
  ·
    refine ⟨419180153569731760196232053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279453435713154506797488035 419180153569731760196232053)
    ·
      refine ⟨39298139397162352518396755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 419180153569731760196232053 39298139397162352518396755)
      ·
        refine ⟨58947209095743528777595133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39298139397162352518396755 58947209095743528777595133)
        ·
          refine ⟨22105203410903823291598175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58947209095743528777595133 22105203410903823291598175)
          ·
            refine ⟨33157805116355734937397263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22105203410903823291598175 33157805116355734937397263)
            ·
              refine ⟨49736707674533602406095895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33157805116355734937397263 49736707674533602406095895)
              ·
                refine ⟨74605061511800403609143843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49736707674533602406095895 74605061511800403609143843)
                ·
                  refine ⟨111907592267700605413715765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74605061511800403609143843 111907592267700605413715765)
                  ·
                    refine ⟨10491336775096931757535853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111907592267700605413715765 10491336775096931757535853)
                    ·
                      refine ⟨3934251290661349409075945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10491336775096931757535853 3934251290661349409075945)
                      ·
                        rfl

theorem cell23_7661927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_7661927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661927 prefixEnd_7661927 := by exact prefixLift 7661927
  have htrace : WordTrace (prefixWord ++ tailWord_7661927) baseStart_7661927 baseEnd_7661927 := by
    simpa [prefixWord, tailWord_7661927, baseEnd_7661927] using wordTrace_append hprefix tailTrace_7661927
  have hstable : (prefixWord ++ tailWord_7661927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661927).length < 2 ^ (prefixWord ++ tailWord_7661927).sum := by decide
  have hdescent : baseEnd_7661927 < baseStart_7661927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661937 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 4, 5, 2]
def baseStart_7661937 : Nat := 118140960795 + 7661937 * 2 ^ 59
def prefixEnd_7661937 : Nat := 4983230072969 + 3 ^ 40 * 7661937 * 2
def baseEnd_7661937 : Nat := 3934256425467894369950899

theorem tailTrace_7661937 : CollatzResearch.WordTrace tailWord_7661937 prefixEnd_7661937 3934256425467894369950899 := by
  unfold tailWord_7661937
  simp only [CollatzResearch.WordTrace]
  refine ⟨279453800443118278505352065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186302533628745519003568043 279453800443118278505352065)
  ·
    refine ⟨209590350332338708879014049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279453800443118278505352065 209590350332338708879014049)
    ·
      refine ⟨157192762749254031659260537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209590350332338708879014049 157192762749254031659260537)
      ·
        refine ⟨117894572061940523744445403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157192762749254031659260537 117894572061940523744445403)
        ·
          refine ⟨176841858092910785616668105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117894572061940523744445403 176841858092910785616668105)
          ·
            refine ⟨132631393569683089212501079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176841858092910785616668105 132631393569683089212501079)
            ·
              refine ⟨198947090354524633818751619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132631393569683089212501079 198947090354524633818751619)
              ·
                refine ⟨298420635531786950728127429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198947090354524633818751619 298420635531786950728127429)
                ·
                  refine ⟨55953869162210053261523893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298420635531786950728127429 55953869162210053261523893)
                  ·
                    refine ⟨5245675233957192493267865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55953869162210053261523893 5245675233957192493267865)
                    ·
                      refine ⟨3934256425467894369950899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245675233957192493267865 3934256425467894369950899)
                      ·
                        rfl

theorem cell23_7661937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_7661937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661937 prefixEnd_7661937 := by exact prefixLift 7661937
  have htrace : WordTrace (prefixWord ++ tailWord_7661937) baseStart_7661937 baseEnd_7661937 := by
    simpa [prefixWord, tailWord_7661937, baseEnd_7661937] using wordTrace_append hprefix tailTrace_7661937
  have hstable : (prefixWord ++ tailWord_7661937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661937).length < 2 ^ (prefixWord ++ tailWord_7661937).sum := by decide
  have hdescent : baseEnd_7661937 < baseStart_7661937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661947 : List Nat := [1, 1, 1, 1, 1, 7, 3, 1, 2, 5]
def baseStart_7661947 : Nat := 118140960795 + 7661947 * 2 ^ 59
def prefixEnd_7661947 : Nat := 4983230072969 + 3 ^ 40 * 7661947 * 2
def baseEnd_7661947 : Nat := 1311420520091479776941951

theorem tailTrace_7661947 : CollatzResearch.WordTrace tailWord_7661947 prefixEnd_7661947 1311420520091479776941951 := by
  unfold tailWord_7661947
  simp only [CollatzResearch.WordTrace]
  refine ⟨279454165173082050213216095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186302776782054700142144063 279454165173082050213216095)
  ·
    refine ⟨419181247759623075319824143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279454165173082050213216095 419181247759623075319824143)
    ·
      refine ⟨628771871639434612979736215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419181247759623075319824143 628771871639434612979736215)
      ·
        refine ⟨943157807459151919469604323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628771871639434612979736215 943157807459151919469604323)
        ·
          refine ⟨1414736711188727879204406485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943157807459151919469604323 1414736711188727879204406485)
          ·
            refine ⟨33157891668485809668853277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1414736711188727879204406485 33157891668485809668853277)
            ·
              refine ⟨12434209375682178625819979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33157891668485809668853277 12434209375682178625819979)
              ·
                refine ⟨18651314063523267938729969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12434209375682178625819979 18651314063523267938729969)
                ·
                  refine ⟨13988485547642450954047477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18651314063523267938729969 13988485547642450954047477)
                  ·
                    refine ⟨1311420520091479776941951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13988485547642450954047477 1311420520091479776941951)
                    ·
                      rfl

theorem cell23_7661947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 5].length) (baseStart_7661947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661947 prefixEnd_7661947 := by exact prefixLift 7661947
  have htrace : WordTrace (prefixWord ++ tailWord_7661947) baseStart_7661947 baseEnd_7661947 := by
    simpa [prefixWord, tailWord_7661947, baseEnd_7661947] using wordTrace_append hprefix tailTrace_7661947
  have hstable : (prefixWord ++ tailWord_7661947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661947).length < 2 ^ (prefixWord ++ tailWord_7661947).sum := by decide
  have hdescent : baseEnd_7661947 < baseStart_7661947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661962 : List Nat := [3, 1, 2, 5, 2, 1, 1, 2, 2, 2, 2]
def baseStart_7661962 : Nat := 118140960795 + 7661962 * 2 ^ 59
def prefixEnd_7661962 : Nat := 4983230072969 + 3 ^ 40 * 7661962 * 2
def baseEnd_7661962 : Nat := 3934269262484256772138285

theorem tailTrace_7661962 : CollatzResearch.WordTrace tailWord_7661962 prefixEnd_7661962 3934269262484256772138285 := by
  unfold tailWord_7661962
  simp only [CollatzResearch.WordTrace]
  refine ⟨69863678067006926943753035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186303141512018471850008093 69863678067006926943753035)
  ·
    refine ⟨104795517100510390415629553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69863678067006926943753035 104795517100510390415629553)
    ·
      refine ⟨78596637825382792811722165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104795517100510390415629553 78596637825382792811722165)
      ·
        refine ⟨7368434796129636826098953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78596637825382792811722165 7368434796129636826098953)
        ·
          refine ⟨5526326097097227619574215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7368434796129636826098953 5526326097097227619574215)
          ·
            refine ⟨8289489145645841429361323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5526326097097227619574215 8289489145645841429361323)
            ·
              refine ⟨12434233718468762144041985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8289489145645841429361323 12434233718468762144041985)
              ·
                refine ⟨9325675288851571608031489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12434233718468762144041985 9325675288851571608031489)
                ·
                  refine ⟨6994256466638678706023617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9325675288851571608031489 6994256466638678706023617)
                  ·
                    refine ⟨5245692349979009029517713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6994256466638678706023617 5245692349979009029517713)
                    ·
                      refine ⟨3934269262484256772138285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245692349979009029517713 3934269262484256772138285)
                      ·
                        rfl

theorem cell23_7661962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_7661962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661962 prefixEnd_7661962 := by exact prefixLift 7661962
  have htrace : WordTrace (prefixWord ++ tailWord_7661962) baseStart_7661962 baseEnd_7661962 := by
    simpa [prefixWord, tailWord_7661962, baseEnd_7661962] using wordTrace_append hprefix tailTrace_7661962
  have hstable : (prefixWord ++ tailWord_7661962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661962).length < 2 ^ (prefixWord ++ tailWord_7661962).sum := by decide
  have hdescent : baseEnd_7661962 < baseStart_7661962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661984 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 2, 4, 2]
def baseStart_7661984 : Nat := 118140960795 + 7661984 * 2 ^ 59
def prefixEnd_7661984 : Nat := 4983230072969 + 3 ^ 40 * 7661984 * 2
def baseEnd_7661984 : Nat := 3934280559058655686063183

theorem tailTrace_7661984 : CollatzResearch.WordTrace tailWord_7661984 prefixEnd_7661984 3934280559058655686063183 := by
  unfold tailWord_7661984
  simp only [CollatzResearch.WordTrace]
  refine ⟨139727757336974002766156503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186303676449298670354875337 139727757336974002766156503)
  ·
    refine ⟨209591636005461004149234755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139727757336974002766156503 209591636005461004149234755)
    ·
      refine ⟨314387454008191506223852133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209591636005461004149234755 314387454008191506223852133)
      ·
        refine ⟨58947647626535907416972275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314387454008191506223852133 58947647626535907416972275)
        ·
          refine ⟨88421471439803861125458413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58947647626535907416972275 88421471439803861125458413)
          ·
            refine ⟨33158051789926447922046905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88421471439803861125458413 33158051789926447922046905)
            ·
              refine ⟨24868538842444835941535179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33158051789926447922046905 24868538842444835941535179)
              ·
                refine ⟨37302808263667253912302769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24868538842444835941535179 37302808263667253912302769)
                ·
                  refine ⟨27977106197750440434227077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37302808263667253912302769 27977106197750440434227077)
                  ·
                    refine ⟨5245707412078207581417577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27977106197750440434227077 5245707412078207581417577)
                    ·
                      refine ⟨3934280559058655686063183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245707412078207581417577 3934280559058655686063183)
                      ·
                        rfl

theorem cell23_7661984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_7661984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661984 prefixEnd_7661984 := by exact prefixLift 7661984
  have htrace : WordTrace (prefixWord ++ tailWord_7661984) baseStart_7661984 baseEnd_7661984 := by
    simpa [prefixWord, tailWord_7661984, baseEnd_7661984] using wordTrace_append hprefix tailTrace_7661984
  have hstable : (prefixWord ++ tailWord_7661984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661984).length < 2 ^ (prefixWord ++ tailWord_7661984).sum := by decide
  have hdescent : baseEnd_7661984 < baseStart_7661984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7661987 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 3]
def baseStart_7661987 : Nat := 118140960795 + 7661987 * 2 ^ 59
def prefixEnd_7661987 : Nat := 4983230072969 + 3 ^ 40 * 7661987 * 2
def baseEnd_7661987 : Nat := 3934282099500619174325669

theorem tailTrace_7661987 : CollatzResearch.WordTrace tailWord_7661987 prefixEnd_7661987 3934282099500619174325669 := by
  unfold tailWord_7661987
  simp only [CollatzResearch.WordTrace]
  refine ⟨279455624092937137044672215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186303749395291424696448143 279455624092937137044672215)
  ·
    refine ⟨419183436139405705567008323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279455624092937137044672215 419183436139405705567008323)
    ·
      refine ⟨628775154209108558350512485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419183436139405705567008323 628775154209108558350512485)
      ·
        refine ⟨117895341414207854690721091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 628775154209108558350512485 117895341414207854690721091)
        ·
          refine ⟨176843012121311782036081637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117895341414207854690721091 176843012121311782036081637)
          ·
            refine ⟨33158064772745959131765307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176843012121311782036081637 33158064772745959131765307)
            ·
              refine ⟨49737097159118938697647961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33158064772745959131765307 49737097159118938697647961)
              ·
                refine ⟨37302822869339204023235971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49737097159118938697647961 37302822869339204023235971)
                ·
                  refine ⟨55954234304008806034853957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37302822869339204023235971 55954234304008806034853957)
                  ·
                    refine ⟨10491418932001651131535117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55954234304008806034853957 10491418932001651131535117)
                    ·
                      refine ⟨3934282099500619174325669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10491418932001651131535117 3934282099500619174325669)
                      ·
                        rfl

theorem cell23_7661987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_7661987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7661987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7661987 prefixEnd_7661987 := by exact prefixLift 7661987
  have htrace : WordTrace (prefixWord ++ tailWord_7661987) baseStart_7661987 baseEnd_7661987 := by
    simpa [prefixWord, tailWord_7661987, baseEnd_7661987] using wordTrace_append hprefix tailTrace_7661987
  have hstable : (prefixWord ++ tailWord_7661987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7661987).length < 2 ^ (prefixWord ++ tailWord_7661987).sum := by decide
  have hdescent : baseEnd_7661987 < baseStart_7661987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7661987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662028 : List Nat := [2, 2, 1, 4, 4, 1, 1, 1, 3, 4]
def baseStart_7662028 : Nat := 118140960795 + 7662028 * 2 ^ 59
def prefixEnd_7662028 : Nat := 4983230072969 + 3 ^ 40 * 7662028 * 2
def baseEnd_7662028 : Nat := 1311434384069151171304327

theorem tailTrace_7662028 : CollatzResearch.WordTrace tailWord_7662028 prefixEnd_7662028 1311434384069151171304327 := by
  unfold tailWord_7662028
  simp only [CollatzResearch.WordTrace]
  refine ⟨139728559742894300523457369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186304746323859067364609825 139728559742894300523457369)
  ·
    refine ⟨104796419807170725392593027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139728559742894300523457369 104796419807170725392593027)
    ·
      refine ⟨157194629710756088088889541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104796419807170725392593027 157194629710756088088889541)
      ·
        refine ⟨29473993070766766516666789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157194629710756088088889541 29473993070766766516666789)
        ·
          refine ⟨5526373700768768721875023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29473993070766766516666789 5526373700768768721875023)
          ·
            refine ⟨8289560551153153082812535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5526373700768768721875023 8289560551153153082812535)
            ·
              refine ⟨12434340826729729624218803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8289560551153153082812535 12434340826729729624218803)
              ·
                refine ⟨18651511240094594436328205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12434340826729729624218803 18651511240094594436328205)
                ·
                  refine ⟨6994316715035472913623077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18651511240094594436328205 6994316715035472913623077)
                  ·
                    refine ⟨1311434384069151171304327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6994316715035472913623077 1311434384069151171304327)
                    ·
                      rfl

theorem cell23_7662028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 3, 4].length) (baseStart_7662028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662028 prefixEnd_7662028 := by exact prefixLift 7662028
  have htrace : WordTrace (prefixWord ++ tailWord_7662028) baseStart_7662028 baseEnd_7662028 := by
    simpa [prefixWord, tailWord_7662028, baseEnd_7662028] using wordTrace_append hprefix tailTrace_7662028
  have hstable : (prefixWord ++ tailWord_7662028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662028).length < 2 ^ (prefixWord ++ tailWord_7662028).sum := by decide
  have hdescent : baseEnd_7662028 < baseStart_7662028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662067 : List Nat := [1, 1, 1, 2, 2, 2, 5, 2, 1, 6]
def baseStart_7662067 : Nat := 118140960795 + 7662067 * 2 ^ 59
def prefixEnd_7662067 : Nat := 4983230072969 + 3 ^ 40 * 7662067 * 2
def baseEnd_7662067 : Nat := 1311441059317659620441767

theorem tailTrace_7662067 : CollatzResearch.WordTrace tailWord_7662067 prefixEnd_7662067 1311441059317659620441767 := by
  unfold tailWord_7662067
  simp only [CollatzResearch.WordTrace]
  refine ⟨279458541932647310707584455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186305694621764873805056303 279458541932647310707584455)
  ·
    refine ⟨419187812898970966061376683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279458541932647310707584455 419187812898970966061376683)
    ·
      refine ⟨628781719348456449092065025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419187812898970966061376683 628781719348456449092065025)
      ·
        refine ⟨471586289511342336819048769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628781719348456449092065025 471586289511342336819048769)
        ·
          refine ⟨353689717133506752614286577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471586289511342336819048769 353689717133506752614286577)
          ·
            refine ⟨265267287850130064460714933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353689717133506752614286577 265267287850130064460714933)
            ·
              refine ⟨24868808235949693543192025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 265267287850130064460714933 24868808235949693543192025)
              ·
                refine ⟨18651606176962270157394019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24868808235949693543192025 18651606176962270157394019)
                ·
                  refine ⟨27977409265443405236091029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18651606176962270157394019 27977409265443405236091029)
                  ·
                    refine ⟨1311441059317659620441767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27977409265443405236091029 1311441059317659620441767)
                    ·
                      rfl

theorem cell23_7662067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 6].length) (baseStart_7662067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662067 prefixEnd_7662067 := by exact prefixLift 7662067
  have htrace : WordTrace (prefixWord ++ tailWord_7662067) baseStart_7662067 baseEnd_7662067 := by
    simpa [prefixWord, tailWord_7662067, baseEnd_7662067] using wordTrace_append hprefix tailTrace_7662067
  have hstable : (prefixWord ++ tailWord_7662067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662067).length < 2 ^ (prefixWord ++ tailWord_7662067).sum := by decide
  have hdescent : baseEnd_7662067 < baseStart_7662067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662104 : List Nat := [2, 1, 2, 3, 3, 1, 1, 3, 1, 2, 4]
def baseStart_7662104 : Nat := 118140960795 + 7662104 * 2 ^ 59
def prefixEnd_7662104 : Nat := 4983230072969 + 3 ^ 40 * 7662104 * 2
def baseEnd_7662104 : Nat := 3934342176737195216562631

theorem tailTrace_7662104 : CollatzResearch.WordTrace tailWord_7662104 prefixEnd_7662104 3934342176737195216562631 := by
  unfold tailWord_7662104
  simp only [CollatzResearch.WordTrace]
  refine ⟨139729945716756633013340683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186306594289008844017787577 139729945716756633013340683)
  ·
    refine ⟨209594918575134949520011025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139729945716756633013340683 209594918575134949520011025)
    ·
      refine ⟨157196188931351212140008269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209594918575134949520011025 157196188931351212140008269)
      ·
        refine ⟨58948570849256704552503101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157196188931351212140008269 58948570849256704552503101)
        ·
          refine ⟨22105714068471264207188663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58948570849256704552503101 22105714068471264207188663)
          ·
            refine ⟨33158571102706896310782995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22105714068471264207188663 33158571102706896310782995)
            ·
              refine ⟨49737856654060344466174493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33158571102706896310782995 49737856654060344466174493)
              ·
                refine ⟨18651696245272629174815435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49737856654060344466174493 18651696245272629174815435)
                ·
                  refine ⟨27977544367908943762223153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18651696245272629174815435 27977544367908943762223153)
                  ·
                    refine ⟨20983158275931707821667365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27977544367908943762223153 20983158275931707821667365)
                    ·
                      refine ⟨3934342176737195216562631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20983158275931707821667365 3934342176737195216562631)
                      ·
                        rfl

theorem cell23_7662104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_7662104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662104 prefixEnd_7662104 := by exact prefixLift 7662104
  have htrace : WordTrace (prefixWord ++ tailWord_7662104) baseStart_7662104 baseEnd_7662104 := by
    simpa [prefixWord, tailWord_7662104, baseEnd_7662104] using wordTrace_append hprefix tailTrace_7662104
  have hstable : (prefixWord ++ tailWord_7662104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662104).length < 2 ^ (prefixWord ++ tailWord_7662104).sum := by decide
  have hdescent : baseEnd_7662104 < baseStart_7662104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662108 : List Nat := [2, 2, 3, 1, 2, 3, 1, 2, 3, 2, 2]
def baseStart_7662108 : Nat := 118140960795 + 7662108 * 2 ^ 59
def prefixEnd_7662108 : Nat := 4983230072969 + 3 ^ 40 * 7662108 * 2
def baseEnd_7662108 : Nat := 3934344230659813200912613

theorem tailTrace_7662108 : CollatzResearch.WordTrace tailWord_7662108 prefixEnd_7662108 3934344230659813200912613 := by
  unfold tailWord_7662108
  simp only [CollatzResearch.WordTrace]
  refine ⟨139730018662749387354913489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186306691550332516473217985 139730018662749387354913489)
  ·
    refine ⟨104797513997062040516185117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139730018662749387354913489 104797513997062040516185117)
    ·
      refine ⟨39299067748898265193569419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104797513997062040516185117 39299067748898265193569419)
      ·
        refine ⟨58948601623347397790354129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39299067748898265193569419 58948601623347397790354129)
        ·
          refine ⟨44211451217510548342765597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58948601623347397790354129 44211451217510548342765597)
          ·
            refine ⟨16579294206566455628537099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44211451217510548342765597 16579294206566455628537099)
            ·
              refine ⟨24868941309849683442805649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16579294206566455628537099 24868941309849683442805649)
              ·
                refine ⟨18651705982387262582104237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24868941309849683442805649 18651705982387262582104237)
                ·
                  refine ⟨6994389743395223468289089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18651705982387262582104237 6994389743395223468289089)
                  ·
                    refine ⟨5245792307546417601216817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6994389743395223468289089 5245792307546417601216817)
                    ·
                      refine ⟨3934344230659813200912613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245792307546417601216817 3934344230659813200912613)
                      ·
                        rfl

theorem cell23_7662108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_7662108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662108 prefixEnd_7662108 := by exact prefixLift 7662108
  have htrace : WordTrace (prefixWord ++ tailWord_7662108) baseStart_7662108 baseEnd_7662108 := by
    simpa [prefixWord, tailWord_7662108, baseEnd_7662108] using wordTrace_append hprefix tailTrace_7662108
  have hstable : (prefixWord ++ tailWord_7662108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662108).length < 2 ^ (prefixWord ++ tailWord_7662108).sum := by decide
  have hdescent : baseEnd_7662108 < baseStart_7662108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662142 : List Nat := [4, 2, 1, 4, 1, 1, 2, 1, 3, 2, 2]
def baseStart_7662142 : Nat := 118140960795 + 7662142 * 2 ^ 59
def prefixEnd_7662142 : Nat := 4983230072969 + 3 ^ 40 * 7662142 * 2
def baseEnd_7662142 : Nat := 3934361689002066067887457

theorem tailTrace_7662142 : CollatzResearch.WordTrace tailWord_7662142 prefixEnd_7662142 3934361689002066067887457 := by
  unfold tailWord_7662142
  simp only [CollatzResearch.WordTrace]
  refine ⟨34932659675921949814570585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186307518271583732344376453 34932659675921949814570585)
  ·
    refine ⟨26199494756941462360927939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34932659675921949814570585 26199494756941462360927939)
    ·
      refine ⟨39299242135412193541391909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26199494756941462360927939 39299242135412193541391909)
      ·
        refine ⟨7368607900389786289010983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39299242135412193541391909 7368607900389786289010983)
        ·
          refine ⟨11052911850584679433516475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7368607900389786289010983 11052911850584679433516475)
          ·
            refine ⟨16579367775877019150274713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11052911850584679433516475 16579367775877019150274713)
            ·
              refine ⟨12434525831907764362706035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16579367775877019150274713 12434525831907764362706035)
              ·
                refine ⟨18651788747861646544059053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12434525831907764362706035 18651788747861646544059053)
                ·
                  refine ⟨6994420780448117454022145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18651788747861646544059053 6994420780448117454022145)
                  ·
                    refine ⟨5245815585336088090516609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6994420780448117454022145 5245815585336088090516609)
                    ·
                      refine ⟨3934361689002066067887457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245815585336088090516609 3934361689002066067887457)
                      ·
                        rfl

theorem cell23_7662142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_7662142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662142 prefixEnd_7662142 := by exact prefixLift 7662142
  have htrace : WordTrace (prefixWord ++ tailWord_7662142) baseStart_7662142 baseEnd_7662142 := by
    simpa [prefixWord, tailWord_7662142, baseEnd_7662142] using wordTrace_append hprefix tailTrace_7662142
  have hstable : (prefixWord ++ tailWord_7662142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662142).length < 2 ^ (prefixWord ++ tailWord_7662142).sum := by decide
  have hdescent : baseEnd_7662142 < baseStart_7662142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662147 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 4]
def baseStart_7662147 : Nat := 118140960795 + 7662147 * 2 ^ 59
def prefixEnd_7662147 : Nat := 4983230072969 + 3 ^ 40 * 7662147 * 2
def baseEnd_7662147 : Nat := 3934364256405338548324933

theorem tailTrace_7662147 : CollatzResearch.WordTrace tailWord_7662147 prefixEnd_7662147 3934364256405338548324933 := by
  unfold tailWord_7662147
  simp only [CollatzResearch.WordTrace]
  refine ⟨279461459772357484370496695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186307639848238322913664463 279461459772357484370496695)
  ·
    refine ⟨419192189658536226555745043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279461459772357484370496695 419192189658536226555745043)
    ·
      refine ⟨628788284487804339833617565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419192189658536226555745043 628788284487804339833617565)
      ·
        refine ⟨235795606682926627437606587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 628788284487804339833617565 235795606682926627437606587)
        ·
          refine ⟨353693410024389941156409881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235795606682926627437606587 353693410024389941156409881)
          ·
            refine ⟨265270057518292455867307411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353693410024389941156409881 265270057518292455867307411)
            ·
              refine ⟨397905086277438683800961117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265270057518292455867307411 397905086277438683800961117)
              ·
                refine ⟨149214407354039506425360419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 397905086277438683800961117 149214407354039506425360419)
                ·
                  refine ⟨223821611031059259638040629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149214407354039506425360419 223821611031059259638040629)
                  ·
                    refine ⟨20983276034161805591066309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 223821611031059259638040629 20983276034161805591066309)
                    ·
                      refine ⟨3934364256405338548324933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20983276034161805591066309 3934364256405338548324933)
                      ·
                        rfl

theorem cell23_7662147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_7662147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662147 prefixEnd_7662147 := by exact prefixLift 7662147
  have htrace : WordTrace (prefixWord ++ tailWord_7662147) baseStart_7662147 baseEnd_7662147 := by
    simpa [prefixWord, tailWord_7662147, baseEnd_7662147] using wordTrace_append hprefix tailTrace_7662147
  have hstable : (prefixWord ++ tailWord_7662147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662147).length < 2 ^ (prefixWord ++ tailWord_7662147).sum := by decide
  have hdescent : baseEnd_7662147 < baseStart_7662147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662204 : List Nat := [2, 2, 2, 1, 1, 2, 5, 1, 7]
def baseStart_7662204 : Nat := 118140960795 + 7662204 * 2 ^ 59
def prefixEnd_7662204 : Nat := 4983230072969 + 3 ^ 40 * 7662204 * 2
def baseEnd_7662204 : Nat := 437154836089182758368019

theorem tailTrace_7662204 : CollatzResearch.WordTrace tailWord_7662204 prefixEnd_7662204 437154836089182758368019 := by
  unfold tailWord_7662204
  simp only [CollatzResearch.WordTrace]
  refine ⟨139731769366575491552660833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186309025822100655403547777 139731769366575491552660833)
  ·
    refine ⟨104798827024931618664495625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139731769366575491552660833 104798827024931618664495625)
    ·
      refine ⟨78599120268698713998371719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104798827024931618664495625 78599120268698713998371719)
      ·
        refine ⟨117898680403048070997557579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78599120268698713998371719 117898680403048070997557579)
        ·
          refine ⟨176848020604572106496336369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117898680403048070997557579 176848020604572106496336369)
          ·
            refine ⟨132636015453429079872252277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176848020604572106496336369 132636015453429079872252277)
            ·
              refine ⟨12434626448758976238023651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132636015453429079872252277 12434626448758976238023651)
              ·
                refine ⟨18651939673138464357035477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12434626448758976238023651 18651939673138464357035477)
                ·
                  refine ⟨437154836089182758368019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18651939673138464357035477 437154836089182758368019)
                  ·
                    rfl

theorem cell23_7662204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 7].length) (baseStart_7662204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662204 prefixEnd_7662204 := by exact prefixLift 7662204
  have htrace : WordTrace (prefixWord ++ tailWord_7662204) baseStart_7662204 baseEnd_7662204 := by
    simpa [prefixWord, tailWord_7662204, baseEnd_7662204] using wordTrace_append hprefix tailTrace_7662204
  have hstable : (prefixWord ++ tailWord_7662204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662204).length < 2 ^ (prefixWord ++ tailWord_7662204).sum := by decide
  have hdescent : baseEnd_7662204 < baseStart_7662204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662207 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 8]
def baseStart_7662207 : Nat := 118140960795 + 7662207 * 2 ^ 59
def prefixEnd_7662207 : Nat := 4983230072969 + 3 ^ 40 * 7662207 * 2
def baseEnd_7662207 : Nat := 3934395065244608313574657

theorem tailTrace_7662207 : CollatzResearch.WordTrace tailWord_7662207 prefixEnd_7662207 3934395065244608313574657 := by
  unfold tailWord_7662207
  simp only [CollatzResearch.WordTrace]
  refine ⟨279463648152140114617680875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186309098768093409745120583 279463648152140114617680875)
  ·
    refine ⟨419195472228210171926521313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279463648152140114617680875 419195472228210171926521313)
    ·
      refine ⟨314396604171157628944890985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419195472228210171926521313 314396604171157628944890985)
      ·
        refine ⟨235797453128368221708668239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314396604171157628944890985 235797453128368221708668239)
        ·
          refine ⟨353696179692552332563002359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235797453128368221708668239 353696179692552332563002359)
          ·
            refine ⟨530544269538828498844503539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353696179692552332563002359 530544269538828498844503539)
            ·
              refine ⟨795816404308242748266755309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530544269538828498844503539 795816404308242748266755309)
              ·
                refine ⟨298431151615591030600033241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 795816404308242748266755309 298431151615591030600033241)
                ·
                  refine ⟨223823363711693272950024931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298431151615591030600033241 223823363711693272950024931)
                  ·
                    refine ⟨335735045567539909425037397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 223823363711693272950024931 335735045567539909425037397)
                    ·
                      refine ⟨3934395065244608313574657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 335735045567539909425037397 3934395065244608313574657)
                      ·
                        rfl

theorem cell23_7662207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_7662207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662207 prefixEnd_7662207 := by exact prefixLift 7662207
  have htrace : WordTrace (prefixWord ++ tailWord_7662207) baseStart_7662207 baseEnd_7662207 := by
    simpa [prefixWord, tailWord_7662207, baseEnd_7662207] using wordTrace_append hprefix tailTrace_7662207
  have hstable : (prefixWord ++ tailWord_7662207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662207).length < 2 ^ (prefixWord ++ tailWord_7662207).sum := by decide
  have hdescent : baseEnd_7662207 < baseStart_7662207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662238 : List Nat := [4, 3, 1, 1, 1, 1, 2, 5, 5]
def baseStart_7662238 : Nat := 118140960795 + 7662238 * 2 ^ 59
def prefixEnd_7662238 : Nat := 4983230072969 + 3 ^ 40 * 7662238 * 2
def baseEnd_7662238 : Nat := 437156775904988632476335

theorem tailTrace_7662238 : CollatzResearch.WordTrace tailWord_7662238 prefixEnd_7662238 437156775904988632476335 := by
  unfold tailWord_7662238
  simp only [CollatzResearch.WordTrace]
  refine ⟨34933097351878475864007421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186309852543351871274706245 34933097351878475864007421)
  ·
    refine ⟨13099911506954428449002783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34933097351878475864007421 13099911506954428449002783)
    ·
      refine ⟨19649867260431642673504175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13099911506954428449002783 19649867260431642673504175)
      ·
        refine ⟨29474800890647464010256263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19649867260431642673504175 29474800890647464010256263)
        ·
          refine ⟨44212201335971196015384395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29474800890647464010256263 44212201335971196015384395)
          ·
            refine ⟨66318302003956794023076593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44212201335971196015384395 66318302003956794023076593)
            ·
              refine ⟨49738726502967595517307445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66318302003956794023076593 49738726502967595517307445)
              ·
                refine ⟨4663005609653212079747573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49738726502967595517307445 4663005609653212079747573)
                ·
                  refine ⟨437156775904988632476335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4663005609653212079747573 437156775904988632476335)
                  ·
                    rfl

theorem cell23_7662238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_7662238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662238 prefixEnd_7662238 := by exact prefixLift 7662238
  have htrace : WordTrace (prefixWord ++ tailWord_7662238) baseStart_7662238 baseEnd_7662238 := by
    simpa [prefixWord, tailWord_7662238, baseEnd_7662238] using wordTrace_append hprefix tailTrace_7662238
  have hstable : (prefixWord ++ tailWord_7662238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662238).length < 2 ^ (prefixWord ++ tailWord_7662238).sum := by decide
  have hdescent : baseEnd_7662238 < baseStart_7662238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662244 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_7662244 : Nat := 118140960795 + 7662244 * 2 ^ 59
def prefixEnd_7662244 : Nat := 4983230072969 + 3 ^ 40 * 7662244 * 2
def baseEnd_7662244 : Nat := 3934414064028824668811987

theorem tailTrace_7662244 : CollatzResearch.WordTrace tailWord_7662244 prefixEnd_7662244 3934414064028824668811987 := by
  unfold tailWord_7662244
  simp only [CollatzResearch.WordTrace]
  refine ⟨139732498826503034968388893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186309998435337379957851857 139732498826503034968388893)
  ·
    refine ⟨52399687059938638113145835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139732498826503034968388893 52399687059938638113145835)
    ·
      refine ⟨78599530589907957169718753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52399687059938638113145835 78599530589907957169718753)
      ·
        refine ⟨58949647942430967877289065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78599530589907957169718753 58949647942430967877289065)
        ·
          refine ⟨44212235956823225907966799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58949647942430967877289065 44212235956823225907966799)
          ·
            refine ⟨66318353935234838861950199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44212235956823225907966799 66318353935234838861950199)
            ·
              refine ⟨99477530902852258292925299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66318353935234838861950199 99477530902852258292925299)
              ·
                refine ⟨149216296354278387439387949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99477530902852258292925299 149216296354278387439387949)
                ·
                  refine ⟨55956111132854395289770481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149216296354278387439387949 55956111132854395289770481)
                  ·
                    refine ⟨41967083349640796467327861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55956111132854395289770481 41967083349640796467327861)
                    ·
                      refine ⟨3934414064028824668811987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41967083349640796467327861 3934414064028824668811987)
                      ·
                        rfl

theorem cell23_7662244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_7662244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662244 prefixEnd_7662244 := by exact prefixLift 7662244
  have htrace : WordTrace (prefixWord ++ tailWord_7662244) baseStart_7662244 baseEnd_7662244 := by
    simpa [prefixWord, tailWord_7662244, baseEnd_7662244] using wordTrace_append hprefix tailTrace_7662244
  have hstable : (prefixWord ++ tailWord_7662244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662244).length < 2 ^ (prefixWord ++ tailWord_7662244).sum := by decide
  have hdescent : baseEnd_7662244 < baseStart_7662244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662261 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_7662261 : Nat := 118140960795 + 7662261 * 2 ^ 59
def prefixEnd_7662261 : Nat := 4983230072969 + 3 ^ 40 * 7662261 * 2
def baseEnd_7662261 : Nat := 3934422793199951102299409

theorem tailTrace_7662261 : CollatzResearch.WordTrace tailWord_7662261 prefixEnd_7662261 3934422793199951102299409 := by
  unfold tailWord_7662261
  simp only [CollatzResearch.WordTrace]
  refine ⟨279465617693944481840146637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186310411795962987893431091 279465617693944481840146637)
  ·
    refine ⟨104799606635229180690054989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279465617693944481840146637 104799606635229180690054989)
    ·
      refine ⟨39299852488210942758770621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104799606635229180690054989 39299852488210942758770621)
      ·
        refine ⟨14737444683079103534538983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39299852488210942758770621 14737444683079103534538983)
        ·
          refine ⟨22106167024618655301808475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14737444683079103534538983 22106167024618655301808475)
          ·
            refine ⟨33159250536927982952712713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22106167024618655301808475 33159250536927982952712713)
            ·
              refine ⟨24869437902695987214534535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33159250536927982952712713 24869437902695987214534535)
              ·
                refine ⟨37304156854043980821801803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24869437902695987214534535 37304156854043980821801803)
                ·
                  refine ⟨55956235281065971232702705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37304156854043980821801803 55956235281065971232702705)
                  ·
                    refine ⟨41967176460799478424527029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55956235281065971232702705 41967176460799478424527029)
                    ·
                      refine ⟨3934422793199951102299409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41967176460799478424527029 3934422793199951102299409)
                      ·
                        rfl

theorem cell23_7662261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_7662261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662261 prefixEnd_7662261 := by exact prefixLift 7662261
  have htrace : WordTrace (prefixWord ++ tailWord_7662261) baseStart_7662261 baseEnd_7662261 := by
    simpa [prefixWord, tailWord_7662261, baseEnd_7662261] using wordTrace_append hprefix tailTrace_7662261
  have hstable : (prefixWord ++ tailWord_7662261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662261).length < 2 ^ (prefixWord ++ tailWord_7662261).sum := by decide
  have hdescent : baseEnd_7662261 < baseStart_7662261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662271 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 1, 6, 2]
def baseStart_7662271 : Nat := 118140960795 + 7662271 * 2 ^ 59
def prefixEnd_7662271 : Nat := 4983230072969 + 3 ^ 40 * 7662271 * 2
def baseEnd_7662271 : Nat := 3934427928006496063174363

theorem tailTrace_7662271 : CollatzResearch.WordTrace tailWord_7662271 prefixEnd_7662271 3934427928006496063174363 := by
  unfold tailWord_7662271
  simp only [CollatzResearch.WordTrace]
  refine ⟨279465982423908253548010667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186310654949272169032007111 279465982423908253548010667)
  ·
    refine ⟨419198973635862380322016001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279465982423908253548010667 419198973635862380322016001)
    ·
      refine ⟨314399230226896785241512001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419198973635862380322016001 314399230226896785241512001)
      ·
        refine ⟨235799422670172588931134001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314399230226896785241512001 235799422670172588931134001)
        ·
          refine ⟨176849567002629441698350501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235799422670172588931134001 176849567002629441698350501)
          ·
            refine ⟨33159293812993020318440719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176849567002629441698350501 33159293812993020318440719)
            ·
              refine ⟨49738940719489530477661079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33159293812993020318440719 49738940719489530477661079)
              ·
                refine ⟨74608411079234295716491619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49738940719489530477661079 74608411079234295716491619)
                ·
                  refine ⟨111912616618851443574737429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74608411079234295716491619 111912616618851443574737429)
                  ·
                    refine ⟨5245903904008661417565817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111912616618851443574737429 5245903904008661417565817)
                    ·
                      refine ⟨3934427928006496063174363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245903904008661417565817 3934427928006496063174363)
                      ·
                        rfl

theorem cell23_7662271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 6, 2].length) (baseStart_7662271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662271 prefixEnd_7662271 := by exact prefixLift 7662271
  have htrace : WordTrace (prefixWord ++ tailWord_7662271) baseStart_7662271 baseEnd_7662271 := by
    simpa [prefixWord, tailWord_7662271, baseEnd_7662271] using wordTrace_append hprefix tailTrace_7662271
  have hstable : (prefixWord ++ tailWord_7662271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662271).length < 2 ^ (prefixWord ++ tailWord_7662271).sum := by decide
  have hdescent : baseEnd_7662271 < baseStart_7662271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662348 : List Nat := [2, 2, 1, 2, 2, 1, 1, 5, 2, 3, 2]
def baseStart_7662348 : Nat := 118140960795 + 7662348 * 2 ^ 59
def prefixEnd_7662348 : Nat := 4983230072969 + 3 ^ 40 * 7662348 * 2
def baseEnd_7662348 : Nat := 3934467466016892261911509

theorem tailTrace_7662348 : CollatzResearch.WordTrace tailWord_7662348 prefixEnd_7662348 3934467466016892261911509 := by
  unfold tailWord_7662348
  simp only [CollatzResearch.WordTrace]
  refine ⟨139734395422314647849281849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186312527229752863799042465 139734395422314647849281849)
  ·
    refine ⟨104800796566735985886961387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139734395422314647849281849 104800796566735985886961387)
    ·
      refine ⟨157201194850103978830442081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104800796566735985886961387 157201194850103978830442081)
      ·
        refine ⟨117900896137577984122831561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157201194850103978830442081 117900896137577984122831561)
        ·
          refine ⟨88425672103183488092123671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117900896137577984122831561 88425672103183488092123671)
          ·
            refine ⟨132638508154775232138185507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88425672103183488092123671 132638508154775232138185507)
            ·
              refine ⟨198957762232162848207278261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132638508154775232138185507 198957762232162848207278261)
              ·
                refine ⟨18652290209265267019432337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198957762232162848207278261 18652290209265267019432337)
                ·
                  refine ⟨13989217656948950264574253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18652290209265267019432337 13989217656948950264574253)
                  ·
                    refine ⟨5245956621355856349215345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13989217656948950264574253 5245956621355856349215345)
                    ·
                      refine ⟨3934467466016892261911509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5245956621355856349215345 3934467466016892261911509)
                      ·
                        rfl

theorem cell23_7662348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_7662348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662348 prefixEnd_7662348 := by exact prefixLift 7662348
  have htrace : WordTrace (prefixWord ++ tailWord_7662348) baseStart_7662348 baseEnd_7662348 := by
    simpa [prefixWord, tailWord_7662348, baseEnd_7662348] using wordTrace_append hprefix tailTrace_7662348
  have hstable : (prefixWord ++ tailWord_7662348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662348).length < 2 ^ (prefixWord ++ tailWord_7662348).sum := by decide
  have hdescent : baseEnd_7662348 < baseStart_7662348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662372 : List Nat := [2, 3, 1, 3, 3, 2, 1, 1, 3, 1, 3]
def baseStart_7662372 : Nat := 118140960795 + 7662372 * 2 ^ 59
def prefixEnd_7662372 : Nat := 4983230072969 + 3 ^ 40 * 7662372 * 2
def baseEnd_7662372 : Nat := 3934479789552600168011399

theorem tailTrace_7662372 : CollatzResearch.WordTrace tailWord_7662372 prefixEnd_7662372 3934479789552600168011399 := by
  unfold tailWord_7662372
  simp only [CollatzResearch.WordTrace]
  refine ⟨139734833098271173898718685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186313110797694898531624913 139734833098271173898718685)
  ·
    refine ⟨52400562411851690212019507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139734833098271173898718685 52400562411851690212019507)
    ·
      refine ⟨78600843617777535318029261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52400562411851690212019507 78600843617777535318029261)
      ·
        refine ⟨29475316356666575744260973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78600843617777535318029261 29475316356666575744260973)
        ·
          refine ⟨11053243633749965904097865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29475316356666575744260973 11053243633749965904097865)
          ·
            refine ⟨8289932725312474428073399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11053243633749965904097865 8289932725312474428073399)
            ·
              refine ⟨12434899087968711642110099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8289932725312474428073399 12434899087968711642110099)
              ·
                refine ⟨18652348631953067463165149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12434899087968711642110099 18652348631953067463165149)
                ·
                  refine ⟨6994630736982400298686931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18652348631953067463165149 6994630736982400298686931)
                  ·
                    refine ⟨10491946105473600448030397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6994630736982400298686931 10491946105473600448030397)
                    ·
                      refine ⟨3934479789552600168011399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10491946105473600448030397 3934479789552600168011399)
                      ·
                        rfl

theorem cell23_7662372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_7662372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662372 prefixEnd_7662372 := by exact prefixLift 7662372
  have htrace : WordTrace (prefixWord ++ tailWord_7662372) baseStart_7662372 baseEnd_7662372 := by
    simpa [prefixWord, tailWord_7662372, baseEnd_7662372] using wordTrace_append hprefix tailTrace_7662372
  have hstable : (prefixWord ++ tailWord_7662372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662372).length < 2 ^ (prefixWord ++ tailWord_7662372).sum := by decide
  have hdescent : baseEnd_7662372 < baseStart_7662372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662391 : List Nat := [1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 4]
def baseStart_7662391 : Nat := 118140960795 + 7662391 * 2 ^ 59
def prefixEnd_7662391 : Nat := 4983230072969 + 3 ^ 40 * 7662391 * 2
def baseEnd_7662391 : Nat := 3934489545685035593673811

theorem tailTrace_7662391 : CollatzResearch.WordTrace tailWord_7662391 prefixEnd_7662391 3934489545685035593673811 := by
  unfold tailWord_7662391
  simp only [CollatzResearch.WordTrace]
  refine ⟨279470359183473514042379027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186313572788982342694919351 279470359183473514042379027)
  ·
    refine ⟨419205538775210271063568541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279470359183473514042379027 419205538775210271063568541)
    ·
      refine ⟨157202077040703851648838203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419205538775210271063568541 157202077040703851648838203)
      ·
        refine ⟨235803115561055777473257305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157202077040703851648838203 235803115561055777473257305)
        ·
          refine ⟨176852336670791833104942979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235803115561055777473257305 176852336670791833104942979)
          ·
            refine ⟨265278505006187749657414469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176852336670791833104942979 265278505006187749657414469)
            ·
              refine ⟨49739719688660203060765213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265278505006187749657414469 49739719688660203060765213)
              ·
                refine ⟨18652394883247576147786955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49739719688660203060765213 18652394883247576147786955)
                ·
                  refine ⟨27978592324871364221680433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18652394883247576147786955 27978592324871364221680433)
                  ·
                    refine ⟨20983944243653523166260325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27978592324871364221680433 20983944243653523166260325)
                    ·
                      refine ⟨3934489545685035593673811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20983944243653523166260325 3934489545685035593673811)
                      ·
                        rfl

theorem cell23_7662391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_7662391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662391 prefixEnd_7662391 := by exact prefixLift 7662391
  have htrace : WordTrace (prefixWord ++ tailWord_7662391) baseStart_7662391 baseEnd_7662391 := by
    simpa [prefixWord, tailWord_7662391, baseEnd_7662391] using wordTrace_append hprefix tailTrace_7662391
  have hstable : (prefixWord ++ tailWord_7662391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662391).length < 2 ^ (prefixWord ++ tailWord_7662391).sum := by decide
  have hdescent : baseEnd_7662391 < baseStart_7662391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662472 : List Nat := [2, 1, 3, 3, 2, 2, 1, 3, 1, 3, 2]
def baseStart_7662472 : Nat := 118140960795 + 7662472 * 2 ^ 59
def prefixEnd_7662472 : Nat := 4983230072969 + 3 ^ 40 * 7662472 * 2
def baseEnd_7662472 : Nat := 3934531137618049776760939

theorem tailTrace_7662472 : CollatzResearch.WordTrace tailWord_7662472 prefixEnd_7662472 3934531137618049776760939 := by
  unfold tailWord_7662472
  simp only [CollatzResearch.WordTrace]
  refine ⟨139736656748090032438038835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186315542330786709917385113 139736656748090032438038835)
  ·
    refine ⟨209604985122135048657058253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139736656748090032438038835 209604985122135048657058253)
    ·
      refine ⟨78601869420800643246396845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209604985122135048657058253 78601869420800643246396845)
      ·
        refine ⟨29475701032800241217398817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78601869420800643246396845 29475701032800241217398817)
        ·
          refine ⟨22106775774600180913049113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29475701032800241217398817 22106775774600180913049113)
          ·
            refine ⟨16580081830950135684786835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22106775774600180913049113 16580081830950135684786835)
            ·
              refine ⟨24870122746425203527180253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16580081830950135684786835 24870122746425203527180253)
              ·
                refine ⟨9326296029909451322692595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24870122746425203527180253 9326296029909451322692595)
                ·
                  refine ⟨13989444044864176984038893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9326296029909451322692595 13989444044864176984038893)
                  ·
                    refine ⟨5246041516824066369014585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13989444044864176984038893 5246041516824066369014585)
                    ·
                      refine ⟨3934531137618049776760939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5246041516824066369014585 3934531137618049776760939)
                      ·
                        rfl

theorem cell23_7662472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_7662472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662472 prefixEnd_7662472 := by exact prefixLift 7662472
  have htrace : WordTrace (prefixWord ++ tailWord_7662472) baseStart_7662472 baseEnd_7662472 := by
    simpa [prefixWord, tailWord_7662472, baseEnd_7662472] using wordTrace_append hprefix tailTrace_7662472
  have hstable : (prefixWord ++ tailWord_7662472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662472).length < 2 ^ (prefixWord ++ tailWord_7662472).sum := by decide
  have hdescent : baseEnd_7662472 < baseStart_7662472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662531 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 5]
def baseStart_7662531 : Nat := 118140960795 + 7662531 * 2 ^ 59
def prefixEnd_7662531 : Nat := 4983230072969 + 3 ^ 40 * 7662531 * 2
def baseEnd_7662531 : Nat := 3934561432976665045923167

theorem tailTrace_7662531 : CollatzResearch.WordTrace tailWord_7662531 prefixEnd_7662531 3934561432976665045923167 := by
  unfold tailWord_7662531
  simp only [CollatzResearch.WordTrace]
  refine ⟨279475465402966317952475447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186316976935310878634983631 279475465402966317952475447)
  ·
    refine ⟨419213198104449476928713171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279475465402966317952475447 419213198104449476928713171)
    ·
      refine ⟨628819797156674215393069757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419213198104449476928713171 628819797156674215393069757)
      ·
        refine ⟨235807423933752830772401159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 628819797156674215393069757 235807423933752830772401159)
        ·
          refine ⟨353711135900629246158601739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235807423933752830772401159 353711135900629246158601739)
          ·
            refine ⟨530566703850943869237902609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353711135900629246158601739 530566703850943869237902609)
            ·
              refine ⟨397925027888207901928426957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530566703850943869237902609 397925027888207901928426957)
              ·
                refine ⟨149221885458077963223160109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 397925027888207901928426957 149221885458077963223160109)
                ·
                  refine ⟨55958207046779236208685041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149221885458077963223160109 55958207046779236208685041)
                  ·
                    refine ⟨41968655285084427156513781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55958207046779236208685041 41968655285084427156513781)
                    ·
                      refine ⟨3934561432976665045923167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41968655285084427156513781 3934561432976665045923167)
                      ·
                        rfl

theorem cell23_7662531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_7662531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662531 prefixEnd_7662531 := by exact prefixLift 7662531
  have htrace : WordTrace (prefixWord ++ tailWord_7662531) baseStart_7662531 baseEnd_7662531 := by
    simpa [prefixWord, tailWord_7662531, baseEnd_7662531] using wordTrace_append hprefix tailTrace_7662531
  have hstable : (prefixWord ++ tailWord_7662531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662531).length < 2 ^ (prefixWord ++ tailWord_7662531).sum := by decide
  have hdescent : baseEnd_7662531 < baseStart_7662531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662542 : List Nat := [4, 1, 1, 1, 2, 4, 3, 2, 5]
def baseStart_7662542 : Nat := 118140960795 + 7662542 * 2 ^ 59
def prefixEnd_7662542 : Nat := 4983230072969 + 3 ^ 40 * 7662542 * 2
def baseEnd_7662542 : Nat := 437174120140429389209513

theorem tailTrace_7662542 : CollatzResearch.WordTrace tailWord_7662542 prefixEnd_7662542 437174120140429389209513 := by
  unfold tailWord_7662542
  simp only [CollatzResearch.WordTrace]
  refine ⟨34934483325740808353890735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186317244403950977887417253 34934483325740808353890735)
  ·
    refine ⟨52401724988611212530836103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34934483325740808353890735 52401724988611212530836103)
    ·
      refine ⟨78602587482916818796254155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52401724988611212530836103 78602587482916818796254155)
      ·
        refine ⟨117903881224375228194381233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78602587482916818796254155 117903881224375228194381233)
        ·
          refine ⟨88427910918281421145785925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117903881224375228194381233 88427910918281421145785925)
          ·
            refine ⟨16580233297177766464834861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88427910918281421145785925 16580233297177766464834861)
            ·
              refine ⟨6217587486441662424313073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16580233297177766464834861 6217587486441662424313073)
              ·
                refine ⟨4663190614831246818234805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6217587486441662424313073 4663190614831246818234805)
                ·
                  refine ⟨437174120140429389209513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4663190614831246818234805 437174120140429389209513)
                  ·
                    rfl

theorem cell23_7662542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_7662542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662542 prefixEnd_7662542 := by exact prefixLift 7662542
  have htrace : WordTrace (prefixWord ++ tailWord_7662542) baseStart_7662542 baseEnd_7662542 := by
    simpa [prefixWord, tailWord_7662542, baseEnd_7662542] using wordTrace_append hprefix tailTrace_7662542
  have hstable : (prefixWord ++ tailWord_7662542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662542).length < 2 ^ (prefixWord ++ tailWord_7662542).sum := by decide
  have hdescent : baseEnd_7662542 < baseStart_7662542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662548 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_7662548 : Nat := 118140960795 + 7662548 * 2 ^ 59
def prefixEnd_7662548 : Nat := 4983230072969 + 3 ^ 40 * 7662548 * 2
def baseEnd_7662548 : Nat := 3934570162147791479410589

theorem tailTrace_7662548 : CollatzResearch.WordTrace tailWord_7662548 prefixEnd_7662548 3934570162147791479410589 := by
  unfold tailWord_7662548
  simp only [CollatzResearch.WordTrace]
  refine ⟨139738042721952364927922149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186317390295936486570562865 139738042721952364927922149)
  ·
    refine ⟨26200883010366068423985403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139738042721952364927922149 26200883010366068423985403)
    ·
      refine ⟨39301324515549102635978105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26200883010366068423985403 39301324515549102635978105)
      ·
        refine ⟨29475993386661826976983579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39301324515549102635978105 29475993386661826976983579)
        ·
          refine ⟨44213990079992740465475369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29475993386661826976983579 44213990079992740465475369)
          ·
            refine ⟨33160492559994555349106527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44213990079992740465475369 33160492559994555349106527)
            ·
              refine ⟨49740738839991833023659791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33160492559994555349106527 49740738839991833023659791)
              ·
                refine ⟨74611108259987749535489687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49740738839991833023659791 74611108259987749535489687)
                ·
                  refine ⟨111916662389981624303234531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74611108259987749535489687 111916662389981624303234531)
                  ·
                    refine ⟨167874993584972436454851797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111916662389981624303234531 167874993584972436454851797)
                    ·
                      refine ⟨3934570162147791479410589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167874993584972436454851797 3934570162147791479410589)
                      ·
                        rfl

theorem cell23_7662548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_7662548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662548 prefixEnd_7662548 := by exact prefixLift 7662548
  have htrace : WordTrace (prefixWord ++ tailWord_7662548) baseStart_7662548 baseEnd_7662548 := by
    simpa [prefixWord, tailWord_7662548, baseEnd_7662548] using wordTrace_append hprefix tailTrace_7662548
  have hstable : (prefixWord ++ tailWord_7662548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662548).length < 2 ^ (prefixWord ++ tailWord_7662548).sum := by decide
  have hdescent : baseEnd_7662548 < baseStart_7662548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662551 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 2, 8]
def baseStart_7662551 : Nat := 118140960795 + 7662551 * 2 ^ 59
def prefixEnd_7662551 : Nat := 4983230072969 + 3 ^ 40 * 7662551 * 2
def baseEnd_7662551 : Nat := 1311523900863251655891025

theorem tailTrace_7662551 : CollatzResearch.WordTrace tailWord_7662551 prefixEnd_7662551 1311523900863251655891025 := by
  unfold tailWord_7662551
  simp only [CollatzResearch.WordTrace]
  refine ⟨279476194862893861368203507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186317463241929240912135671 279476194862893861368203507)
  ·
    refine ⟨419214292294340792052305261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279476194862893861368203507 419214292294340792052305261)
    ·
      refine ⟨157205359610377797019614473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419214292294340792052305261 157205359610377797019614473)
      ·
        refine ⟨117904019707783347764710855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157205359610377797019614473 117904019707783347764710855)
        ·
          refine ⟨176856029561675021647066283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117904019707783347764710855 176856029561675021647066283)
          ·
            refine ⟨265284044342512532470599425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176856029561675021647066283 265284044342512532470599425)
            ·
              refine ⟨198963033256884399352949569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265284044342512532470599425 198963033256884399352949569)
              ·
                refine ⟨149222274942663299514712177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198963033256884399352949569 149222274942663299514712177)
                ·
                  refine ⟨111916706206997474636034133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149222274942663299514712177 111916706206997474636034133)
                  ·
                    refine ⟨1311523900863251655891025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111916706206997474636034133 1311523900863251655891025)
                    ·
                      rfl

theorem cell23_7662551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_7662551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662551 prefixEnd_7662551 := by exact prefixLift 7662551
  have htrace : WordTrace (prefixWord ++ tailWord_7662551) baseStart_7662551 baseEnd_7662551 := by
    simpa [prefixWord, tailWord_7662551, baseEnd_7662551] using wordTrace_append hprefix tailTrace_7662551
  have hstable : (prefixWord ++ tailWord_7662551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662551).length < 2 ^ (prefixWord ++ tailWord_7662551).sum := by decide
  have hdescent : baseEnd_7662551 < baseStart_7662551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662571 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 6]
def baseStart_7662571 : Nat := 118140960795 + 7662571 * 2 ^ 59
def prefixEnd_7662571 : Nat := 4983230072969 + 3 ^ 40 * 7662571 * 2
def baseEnd_7662571 : Nat := 3934581972202844889422983

theorem tailTrace_7662571 : CollatzResearch.WordTrace tailWord_7662571 prefixEnd_7662571 3934581972202844889422983 := by
  unfold tailWord_7662571
  simp only [CollatzResearch.WordTrace]
  refine ⟨279476924322821404783931567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186317949548547603189287711 279476924322821404783931567)
  ·
    refine ⟨419215386484232107175897351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279476924322821404783931567 419215386484232107175897351)
    ·
      refine ⟨628823079726348160763846027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419215386484232107175897351 628823079726348160763846027)
      ·
        refine ⟨943234619589522241145769041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628823079726348160763846027 943234619589522241145769041)
        ·
          refine ⟨707425964692141680859326781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 943234619589522241145769041 707425964692141680859326781)
          ·
            refine ⟨265284736759553130322247543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 707425964692141680859326781 265284736759553130322247543)
            ·
              refine ⟨397927105139329695483371315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265284736759553130322247543 397927105139329695483371315)
              ·
                refine ⟨596890657708994543225056973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397927105139329695483371315 596890657708994543225056973)
                ·
                  refine ⟨223833996640872953709396365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596890657708994543225056973 223833996640872953709396365)
                  ·
                    refine ⟨83937748740327357641023637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 223833996640872953709396365 83937748740327357641023637)
                    ·
                      refine ⟨3934581972202844889422983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83937748740327357641023637 3934581972202844889422983)
                      ·
                        rfl

theorem cell23_7662571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 6].length) (baseStart_7662571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662571 prefixEnd_7662571 := by exact prefixLift 7662571
  have htrace : WordTrace (prefixWord ++ tailWord_7662571) baseStart_7662571 baseEnd_7662571 := by
    simpa [prefixWord, tailWord_7662571, baseEnd_7662571] using wordTrace_append hprefix tailTrace_7662571
  have hstable : (prefixWord ++ tailWord_7662571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662571).length < 2 ^ (prefixWord ++ tailWord_7662571).sum := by decide
  have hdescent : baseEnd_7662571 < baseStart_7662571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662575 : List Nat := [1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 4]
def baseStart_7662575 : Nat := 118140960795 + 7662575 * 2 ^ 59
def prefixEnd_7662575 : Nat := 4983230072969 + 3 ^ 40 * 7662575 * 2
def baseEnd_7662575 : Nat := 3934584026125462873772965

theorem tailTrace_7662575 : CollatzResearch.WordTrace tailWord_7662575 prefixEnd_7662575 3934584026125462873772965 := by
  unfold tailWord_7662575
  simp only [CollatzResearch.WordTrace]
  refine ⟨279477070214806913467077179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186318046809871275644718119 279477070214806913467077179)
  ·
    refine ⟨419215605322210370200615769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279477070214806913467077179 419215605322210370200615769)
    ·
      refine ⟨314411703991657777650461827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419215605322210370200615769 314411703991657777650461827)
      ·
        refine ⟨471617555987486666475692741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314411703991657777650461827 471617555987486666475692741)
        ·
          refine ⟨88428291747653749964192389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 471617555987486666475692741 88428291747653749964192389)
          ·
            refine ⟨16580304702685078118286073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88428291747653749964192389 16580304702685078118286073)
            ·
              refine ⟨12435228527013808588714555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16580304702685078118286073 12435228527013808588714555)
              ·
                refine ⟨18652842790520712883071833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12435228527013808588714555 18652842790520712883071833)
                ·
                  refine ⟨13989632092890534662303875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18652842790520712883071833 13989632092890534662303875)
                  ·
                    refine ⟨20984448139335801993455813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13989632092890534662303875 20984448139335801993455813)
                    ·
                      refine ⟨3934584026125462873772965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20984448139335801993455813 3934584026125462873772965)
                      ·
                        rfl

theorem cell23_7662575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 4].length) (baseStart_7662575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662575 prefixEnd_7662575 := by exact prefixLift 7662575
  have htrace : WordTrace (prefixWord ++ tailWord_7662575) baseStart_7662575 baseEnd_7662575 := by
    simpa [prefixWord, tailWord_7662575, baseEnd_7662575] using wordTrace_append hprefix tailTrace_7662575
  have hstable : (prefixWord ++ tailWord_7662575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662575).length < 2 ^ (prefixWord ++ tailWord_7662575).sum := by decide
  have hdescent : baseEnd_7662575 < baseStart_7662575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662615 : List Nat := [1, 1, 3, 5, 1, 1, 2, 3, 6]
def baseStart_7662615 : Nat := 118140960795 + 7662615 * 2 ^ 59
def prefixEnd_7662615 : Nat := 4983230072969 + 3 ^ 40 * 7662615 * 2
def baseEnd_7662615 : Nat := 437178285039071413030309

theorem tailTrace_7662615 : CollatzResearch.WordTrace tailWord_7662615 prefixEnd_7662615 437178285039071413030309 := by
  unfold tailWord_7662615
  simp only [CollatzResearch.WordTrace]
  refine ⟨279478529134662000298533299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186319019423108000199022199 279478529134662000298533299)
  ·
    refine ⟨419217793701993000447799949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279478529134662000298533299 419217793701993000447799949)
    ·
      refine ⟨157206672638247375167924981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419217793701993000447799949 157206672638247375167924981)
      ·
        refine ⟨14738125559835691421992967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157206672638247375167924981 14738125559835691421992967)
        ·
          refine ⟨22107188339753537132989451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14738125559835691421992967 22107188339753537132989451)
          ·
            refine ⟨33160782509630305699484177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22107188339753537132989451 33160782509630305699484177)
            ·
              refine ⟨24870586882222729274613133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33160782509630305699484177 24870586882222729274613133)
              ·
                refine ⟨9326470080833523477979925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24870586882222729274613133 9326470080833523477979925)
                ·
                  refine ⟨437178285039071413030309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9326470080833523477979925 437178285039071413030309)
                  ·
                    rfl

theorem cell23_7662615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 6].length) (baseStart_7662615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662615 prefixEnd_7662615 := by exact prefixLift 7662615
  have htrace : WordTrace (prefixWord ++ tailWord_7662615) baseStart_7662615 baseEnd_7662615 := by
    simpa [prefixWord, tailWord_7662615, baseEnd_7662615] using wordTrace_append hprefix tailTrace_7662615
  have hstable : (prefixWord ++ tailWord_7662615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662615).length < 2 ^ (prefixWord ++ tailWord_7662615).sum := by decide
  have hdescent : baseEnd_7662615 < baseStart_7662615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662635 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 1, 5, 2]
def baseStart_7662635 : Nat := 118140960795 + 7662635 * 2 ^ 59
def prefixEnd_7662635 : Nat := 4983230072969 + 3 ^ 40 * 7662635 * 2
def baseEnd_7662635 : Nat := 3934614834964732639022689

theorem tailTrace_7662635 : CollatzResearch.WordTrace tailWord_7662635 prefixEnd_7662635 3934614834964732639022689 := by
  unfold tailWord_7662635
  simp only [CollatzResearch.WordTrace]
  refine ⟨279479258594589543714261359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186319505729726362476174239 279479258594589543714261359)
  ·
    refine ⟨419218887891884315571392039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279479258594589543714261359 419218887891884315571392039)
    ·
      refine ⟨628828331837826473357088059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419218887891884315571392039 628828331837826473357088059)
      ·
        refine ⟨943242497756739710035632089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628828331837826473357088059 943242497756739710035632089)
        ·
          refine ⟨707431873317554782526724067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 943242497756739710035632089 707431873317554782526724067)
          ·
            refine ⟨1061147809976332173790086101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707431873317554782526724067 1061147809976332173790086101)
            ·
              refine ⟨24870651796320285323205143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1061147809976332173790086101 24870651796320285323205143)
              ·
                refine ⟨37305977694480427984807715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24870651796320285323205143 37305977694480427984807715)
                ·
                  refine ⟨55958966541720641977211573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37305977694480427984807715 55958966541720641977211573)
                  ·
                    refine ⟨5246153113286310185363585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55958966541720641977211573 5246153113286310185363585)
                    ·
                      refine ⟨3934614834964732639022689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5246153113286310185363585 3934614834964732639022689)
                      ·
                        rfl

theorem cell23_7662635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 5, 2].length) (baseStart_7662635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662635 prefixEnd_7662635 := by exact prefixLift 7662635
  have htrace : WordTrace (prefixWord ++ tailWord_7662635) baseStart_7662635 baseEnd_7662635 := by
    simpa [prefixWord, tailWord_7662635, baseEnd_7662635] using wordTrace_append hprefix tailTrace_7662635
  have hstable : (prefixWord ++ tailWord_7662635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662635).length < 2 ^ (prefixWord ++ tailWord_7662635).sum := by decide
  have hdescent : baseEnd_7662635 < baseStart_7662635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662682 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2]
def baseStart_7662682 : Nat := 118140960795 + 7662682 * 2 ^ 59
def prefixEnd_7662682 : Nat := 4983230072969 + 3 ^ 40 * 7662682 * 2
def baseEnd_7662682 : Nat := 3934638968555493955134973

theorem tailTrace_7662682 : CollatzResearch.WordTrace tailWord_7662682 prefixEnd_7662682 3934638968555493955134973 := by
  unfold tailWord_7662682
  simp only [CollatzResearch.WordTrace]
  refine ⟨69870243206354817685305575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186320648550279513827481533 69870243206354817685305575)
  ·
    refine ⟨104805364809532226527958363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69870243206354817685305575 104805364809532226527958363)
    ·
      refine ⟨157208047214298339791937545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104805364809532226527958363 157208047214298339791937545)
      ·
        refine ⟨117906035410723754843953159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157208047214298339791937545 117906035410723754843953159)
        ·
          refine ⟨176859053116085632265929739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117906035410723754843953159 176859053116085632265929739)
          ·
            refine ⟨265288579674128448398894609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176859053116085632265929739 265288579674128448398894609)
            ·
              refine ⟨198966434755596336299170957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265288579674128448398894609 198966434755596336299170957)
              ·
                refine ⟨74612413033348626112189109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198966434755596336299170957 74612413033348626112189109)
                ·
                  refine ⟨6994913721876433698017729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74612413033348626112189109 6994913721876433698017729)
                  ·
                    refine ⟨5246185291407325273513297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6994913721876433698017729 5246185291407325273513297)
                    ·
                      refine ⟨3934638968555493955134973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5246185291407325273513297 3934638968555493955134973)
                      ·
                        rfl

theorem cell23_7662682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_7662682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662682 prefixEnd_7662682 := by exact prefixLift 7662682
  have htrace : WordTrace (prefixWord ++ tailWord_7662682) baseStart_7662682 baseEnd_7662682 := by
    simpa [prefixWord, tailWord_7662682, baseEnd_7662682] using wordTrace_append hprefix tailTrace_7662682
  have hstable : (prefixWord ++ tailWord_7662682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662682).length < 2 ^ (prefixWord ++ tailWord_7662682).sum := by decide
  have hdescent : baseEnd_7662682 < baseStart_7662682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662686 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_7662686 : Nat := 118140960795 + 7662686 * 2 ^ 59
def prefixEnd_7662686 : Nat := 4983230072969 + 3 ^ 40 * 7662686 * 2
def baseEnd_7662686 : Nat := 3934641022478111939484955

theorem tailTrace_7662686 : CollatzResearch.WordTrace tailWord_7662686 prefixEnd_7662686 3934641022478111939484955 := by
  unfold tailWord_7662686
  simp only [CollatzResearch.WordTrace]
  refine ⟨34935139839675597428045989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186320745811603186282911941 34935139839675597428045989)
  ·
    refine ⟨6550338719939174517758623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34935139839675597428045989 6550338719939174517758623)
    ·
      refine ⟨9825508079908761776637935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6550338719939174517758623 9825508079908761776637935)
      ·
        refine ⟨14738262119863142664956903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9825508079908761776637935 14738262119863142664956903)
        ·
          refine ⟨22107393179794713997435355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14738262119863142664956903 22107393179794713997435355)
          ·
            refine ⟨33161089769692070996153033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22107393179794713997435355 33161089769692070996153033)
            ·
              refine ⟨24870817327269053247114775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33161089769692070996153033 24870817327269053247114775)
              ·
                refine ⟨37306225990903579870672163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24870817327269053247114775 37306225990903579870672163)
                ·
                  refine ⟨55959338986355369806008245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37306225990903579870672163 55959338986355369806008245)
                  ·
                    refine ⟨5246188029970815919313273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55959338986355369806008245 5246188029970815919313273)
                    ·
                      refine ⟨3934641022478111939484955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5246188029970815919313273 3934641022478111939484955)
                      ·
                        rfl

theorem cell23_7662686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_7662686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662686 prefixEnd_7662686 := by exact prefixLift 7662686
  have htrace : WordTrace (prefixWord ++ tailWord_7662686) baseStart_7662686 baseEnd_7662686 := by
    simpa [prefixWord, tailWord_7662686, baseEnd_7662686] using wordTrace_append hprefix tailTrace_7662686
  have hstable : (prefixWord ++ tailWord_7662686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662686).length < 2 ^ (prefixWord ++ tailWord_7662686).sum := by decide
  have hdescent : baseEnd_7662686 < baseStart_7662686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662688 : List Nat := [2, 1, 1, 3, 2, 2, 3, 9]
def baseStart_7662688 : Nat := 118140960795 + 7662688 * 2 ^ 59
def prefixEnd_7662688 : Nat := 4983230072969 + 3 ^ 40 * 7662688 * 2
def baseEnd_7662688 : Nat := 145727483312571145617035

theorem tailTrace_7662688 : CollatzResearch.WordTrace tailWord_7662688 prefixEnd_7662688 145727483312571145617035 := by
  unfold tailWord_7662688
  simp only [CollatzResearch.WordTrace]
  refine ⟨139740595831698766882970359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186320794442265022510627145 139740595831698766882970359)
  ·
    refine ⟨209610893747548150324455539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139740595831698766882970359 209610893747548150324455539)
    ·
      refine ⟨314416340621322225486683309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209610893747548150324455539 314416340621322225486683309)
      ·
        refine ⟨117906127732995834557506241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314416340621322225486683309 117906127732995834557506241)
        ·
          refine ⟨88429595799746875918129681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117906127732995834557506241 88429595799746875918129681)
          ·
            refine ⟨66322196849810156938597261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88429595799746875918129681 66322196849810156938597261)
            ·
              refine ⟨24870823818678808851973973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66322196849810156938597261 24870823818678808851973973)
              ·
                refine ⟨145727483312571145617035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24870823818678808851973973 145727483312571145617035)
                ·
                  rfl

theorem cell23_7662688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 9].length) (baseStart_7662688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662688 prefixEnd_7662688 := by exact prefixLift 7662688
  have htrace : WordTrace (prefixWord ++ tailWord_7662688) baseStart_7662688 baseEnd_7662688 := by
    simpa [prefixWord, tailWord_7662688, baseEnd_7662688] using wordTrace_append hprefix tailTrace_7662688
  have hstable : (prefixWord ++ tailWord_7662688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662688).length < 2 ^ (prefixWord ++ tailWord_7662688).sum := by decide
  have hdescent : baseEnd_7662688 < baseStart_7662688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662702 : List Nat := [4, 1, 2, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_7662702 : Nat := 118140960795 + 7662702 * 2 ^ 59
def prefixEnd_7662702 : Nat := 4983230072969 + 3 ^ 40 * 7662702 * 2
def baseEnd_7662702 : Nat := 3934649238168583876884881

theorem tailTrace_7662702 : CollatzResearch.WordTrace tailWord_7662702 prefixEnd_7662702 3934649238168583876884881 := by
  unfold tailWord_7662702
  simp only [CollatzResearch.WordTrace]
  refine ⟨34935212785668351769618795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186321134856897876104633573 34935212785668351769618795)
  ·
    refine ⟨52402819178502527654428193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34935212785668351769618795 52402819178502527654428193)
    ·
      refine ⟨39302114383876895740821145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52402819178502527654428193 39302114383876895740821145)
      ·
        refine ⟨29476585787907671805615859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39302114383876895740821145 29476585787907671805615859)
        ·
          refine ⟨44214878681861507708423789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29476585787907671805615859 44214878681861507708423789)
          ·
            refine ⟨16580579505698065390658921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44214878681861507708423789 16580579505698065390658921)
            ·
              refine ⟨12435434629273549042994191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16580579505698065390658921 12435434629273549042994191)
              ·
                refine ⟨18653151943910323564491287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12435434629273549042994191 18653151943910323564491287)
                ·
                  refine ⟨27979727915865485346736931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18653151943910323564491287 27979727915865485346736931)
                  ·
                    refine ⟨41969591873798228020105397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27979727915865485346736931 41969591873798228020105397)
                    ·
                      refine ⟨3934649238168583876884881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41969591873798228020105397 3934649238168583876884881)
                      ·
                        rfl

theorem cell23_7662702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_7662702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662702 prefixEnd_7662702 := by exact prefixLift 7662702
  have htrace : WordTrace (prefixWord ++ tailWord_7662702) baseStart_7662702 baseEnd_7662702 := by
    simpa [prefixWord, tailWord_7662702, baseEnd_7662702] using wordTrace_append hprefix tailTrace_7662702
  have hstable : (prefixWord ++ tailWord_7662702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662702).length < 2 ^ (prefixWord ++ tailWord_7662702).sum := by decide
  have hdescent : baseEnd_7662702 < baseStart_7662702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662775 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 3]
def baseStart_7662775 : Nat := 118140960795 + 7662775 * 2 ^ 59
def prefixEnd_7662775 : Nat := 4983230072969 + 3 ^ 40 * 7662775 * 2
def baseEnd_7662775 : Nat := 3934686722256362091272045

theorem tailTrace_7662775 : CollatzResearch.WordTrace tailWord_7662775 prefixEnd_7662775 3934686722256362091272045 := by
  unfold tailWord_7662775
  simp only [CollatzResearch.WordTrace]
  refine ⟨279484364814082347624357779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186322909876054898416238519 279484364814082347624357779)
  ·
    refine ⟨419226547221123521436536669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279484364814082347624357779 419226547221123521436536669)
    ·
      refine ⟨157209955207921320538701251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419226547221123521436536669 157209955207921320538701251)
      ·
        refine ⟨235814932811881980808051877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157209955207921320538701251 235814932811881980808051877)
        ·
          refine ⟨44215299902227871401509727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235814932811881980808051877 44215299902227871401509727)
          ·
            refine ⟨66322949853341807102264591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44215299902227871401509727 66322949853341807102264591)
            ·
              refine ⟨99484424780012710653396887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66322949853341807102264591 99484424780012710653396887)
              ·
                refine ⟨149226637170019065980095331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99484424780012710653396887 149226637170019065980095331)
                ·
                  refine ⟨223839955755028598970142997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149226637170019065980095331 223839955755028598970142997)
                  ·
                    refine ⟨10492497926016965576725453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 223839955755028598970142997 10492497926016965576725453)
                    ·
                      refine ⟨3934686722256362091272045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10492497926016965576725453 3934686722256362091272045)
                      ·
                        rfl

theorem cell23_7662775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_7662775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662775 prefixEnd_7662775 := by exact prefixLift 7662775
  have htrace : WordTrace (prefixWord ++ tailWord_7662775) baseStart_7662775 baseEnd_7662775 := by
    simpa [prefixWord, tailWord_7662775, baseEnd_7662775] using wordTrace_append hprefix tailTrace_7662775
  have hstable : (prefixWord ++ tailWord_7662775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662775).length < 2 ^ (prefixWord ++ tailWord_7662775).sum := by decide
  have hdescent : baseEnd_7662775 < baseStart_7662775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662782 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_7662782 : Nat := 118140960795 + 7662782 * 2 ^ 59
def prefixEnd_7662782 : Nat := 4983230072969 + 3 ^ 40 * 7662782 * 2
def baseEnd_7662782 : Nat := 1311563438873647854628171

theorem tailTrace_7662782 : CollatzResearch.WordTrace tailWord_7662782 prefixEnd_7662782 1311563438873647854628171 := by
  unfold tailWord_7662782
  simp only [CollatzResearch.WordTrace]
  refine ⟨34935577515632123477482825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186323080083371325213241733 34935577515632123477482825)
  ·
    refine ⟨26201683136724092608112119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34935577515632123477482825 26201683136724092608112119)
    ·
      refine ⟨39302524705086138912168179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26201683136724092608112119 39302524705086138912168179)
      ·
        refine ⟨58953787057629208368252269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39302524705086138912168179 58953787057629208368252269)
        ·
          refine ⟨22107670146610953138094601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58953787057629208368252269 22107670146610953138094601)
          ·
            refine ⟨16580752609958214853570951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22107670146610953138094601 16580752609958214853570951)
            ·
              refine ⟨24871128914937322280356427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16580752609958214853570951 24871128914937322280356427)
              ·
                refine ⟨37306693372405983420534641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24871128914937322280356427 37306693372405983420534641)
                ·
                  refine ⟨27980020029304487565400981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37306693372405983420534641 27980020029304487565400981)
                  ·
                    refine ⟨1311563438873647854628171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27980020029304487565400981 1311563438873647854628171)
                    ·
                      rfl

theorem cell23_7662782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_7662782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662782 prefixEnd_7662782 := by exact prefixLift 7662782
  have htrace : WordTrace (prefixWord ++ tailWord_7662782) baseStart_7662782 baseEnd_7662782 := by
    simpa [prefixWord, tailWord_7662782, baseEnd_7662782] using wordTrace_append hprefix tailTrace_7662782
  have hstable : (prefixWord ++ tailWord_7662782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662782).length < 2 ^ (prefixWord ++ tailWord_7662782).sum := by decide
  have hdescent : baseEnd_7662782 < baseStart_7662782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662829 : List Nat := [1, 5, 1, 2, 2, 1, 2, 4, 5]
def baseStart_7662829 : Nat := 118140960795 + 7662829 * 2 ^ 59
def prefixEnd_7662829 : Nat := 4983230072969 + 3 ^ 40 * 7662829 * 2
def baseEnd_7662829 : Nat := 437190494467967208888533

theorem tailTrace_7662829 : CollatzResearch.WordTrace tailWord_7662829 prefixEnd_7662829 437190494467967208888533 := by
  unfold tailWord_7662829
  simp only [CollatzResearch.WordTrace]
  refine ⟨279486334355886714846823541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186324222903924476564549027 279486334355886714846823541)
  ·
    refine ⟨26201843845864379516889707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279486334355886714846823541 26201843845864379516889707)
    ·
      refine ⟨39302765768796569275334561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26201843845864379516889707 39302765768796569275334561)
      ·
        refine ⟨29477074326597426956500921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39302765768796569275334561 29477074326597426956500921)
        ·
          refine ⟨22107805744948070217375691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29477074326597426956500921 22107805744948070217375691)
          ·
            refine ⟨33161708617422105326063537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22107805744948070217375691 33161708617422105326063537)
            ·
              refine ⟨24871281463066578994547653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33161708617422105326063537 24871281463066578994547653)
              ·
                refine ⟨4663365274324983561477685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24871281463066578994547653 4663365274324983561477685)
                ·
                  refine ⟨437190494467967208888533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4663365274324983561477685 437190494467967208888533)
                  ·
                    rfl

theorem cell23_7662829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_7662829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662829 prefixEnd_7662829 := by exact prefixLift 7662829
  have htrace : WordTrace (prefixWord ++ tailWord_7662829) baseStart_7662829 baseEnd_7662829 := by
    simpa [prefixWord, tailWord_7662829, baseEnd_7662829] using wordTrace_append hprefix tailTrace_7662829
  have hstable : (prefixWord ++ tailWord_7662829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662829).length < 2 ^ (prefixWord ++ tailWord_7662829).sum := by decide
  have hdescent : baseEnd_7662829 < baseStart_7662829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662862 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_7662862 : Nat := 118140960795 + 7662862 * 2 ^ 59
def prefixEnd_7662862 : Nat := 4983230072969 + 3 ^ 40 * 7662862 * 2
def baseEnd_7662862 : Nat := 3934731395073303250884145

theorem tailTrace_7662862 : CollatzResearch.WordTrace tailWord_7662862 prefixEnd_7662862 3934731395073303250884145 := by
  unfold tailWord_7662862
  simp only [CollatzResearch.WordTrace]
  refine ⟨34935942245595895185346855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186325025309844774321849893 34935942245595895185346855)
  ·
    refine ⟨52403913368393842778020283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34935942245595895185346855 52403913368393842778020283)
    ·
      refine ⟨78605870052590764167030425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52403913368393842778020283 78605870052590764167030425)
      ·
        refine ⟨58954402539443073125272819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78605870052590764167030425 58954402539443073125272819)
        ·
          refine ⟨88431603809164609687909229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58954402539443073125272819 88431603809164609687909229)
          ·
            refine ⟨33161851428436728632965961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88431603809164609687909229 33161851428436728632965961)
            ·
              refine ⟨24871388571327546474724471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33161851428436728632965961 24871388571327546474724471)
              ·
                refine ⟨37307082856991319712086707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24871388571327546474724471 37307082856991319712086707)
                ·
                  refine ⟨55960624285486979568130061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37307082856991319712086707 55960624285486979568130061)
                  ·
                    refine ⟨20985234107057617338048773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55960624285486979568130061 20985234107057617338048773)
                    ·
                      refine ⟨3934731395073303250884145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20985234107057617338048773 3934731395073303250884145)
                      ·
                        rfl

theorem cell23_7662862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_7662862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662862 prefixEnd_7662862 := by exact prefixLift 7662862
  have htrace : WordTrace (prefixWord ++ tailWord_7662862) baseStart_7662862 baseEnd_7662862 := by
    simpa [prefixWord, tailWord_7662862, baseEnd_7662862] using wordTrace_append hprefix tailTrace_7662862
  have hstable : (prefixWord ++ tailWord_7662862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662862).length < 2 ^ (prefixWord ++ tailWord_7662862).sum := by decide
  have hdescent : baseEnd_7662862 < baseStart_7662862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662879 : List Nat := [1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 4]
def baseStart_7662879 : Nat := 118140960795 + 7662879 * 2 ^ 59
def prefixEnd_7662879 : Nat := 4983230072969 + 3 ^ 40 * 7662879 * 2
def baseEnd_7662879 : Nat := 3934740124244429684371567

theorem tailTrace_7662879 : CollatzResearch.WordTrace tailWord_7662879 prefixEnd_7662879 3934740124244429684371567 := by
  unfold tailWord_7662879
  simp only [CollatzResearch.WordTrace]
  refine ⟨279488158005705573386143691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186325438670470382257429127 279488158005705573386143691)
  ·
    refine ⟨419232237008558360079215537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279488158005705573386143691 419232237008558360079215537)
    ·
      refine ⟨314424177756418770059411653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419232237008558360079215537 314424177756418770059411653)
      ·
        refine ⟨58954533329328519386139685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314424177756418770059411653 58954533329328519386139685)
        ·
          refine ⟨11053974999249097384901191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58954533329328519386139685 11053974999249097384901191)
          ·
            refine ⟨16580962498873646077351787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11053974999249097384901191 16580962498873646077351787)
            ·
              refine ⟨24871443748310469116027681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16580962498873646077351787 24871443748310469116027681)
              ·
                refine ⟨18653582811232851837020761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24871443748310469116027681 18653582811232851837020761)
                ·
                  refine ⟨13990187108424638877765571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18653582811232851837020761 13990187108424638877765571)
                  ·
                    refine ⟨20985280662636958316648357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13990187108424638877765571 20985280662636958316648357)
                    ·
                      refine ⟨3934740124244429684371567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20985280662636958316648357 3934740124244429684371567)
                      ·
                        rfl

theorem cell23_7662879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_7662879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662879 prefixEnd_7662879 := by exact prefixLift 7662879
  have htrace : WordTrace (prefixWord ++ tailWord_7662879) baseStart_7662879 baseEnd_7662879 := by
    simpa [prefixWord, tailWord_7662879, baseEnd_7662879] using wordTrace_append hprefix tailTrace_7662879
  have hstable : (prefixWord ++ tailWord_7662879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662879).length < 2 ^ (prefixWord ++ tailWord_7662879).sum := by decide
  have hdescent : baseEnd_7662879 < baseStart_7662879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662916 : List Nat := [2, 3, 4, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_7662916 : Nat := 118140960795 + 7662916 * 2 ^ 59
def prefixEnd_7662916 : Nat := 4983230072969 + 3 ^ 40 * 7662916 * 2
def baseEnd_7662916 : Nat := 3934759123028646039608897

theorem tailTrace_7662916 : CollatzResearch.WordTrace tailWord_7662916 prefixEnd_7662916 3934759123028646039608897 := by
  unfold tailWord_7662916
  simp only [CollatzResearch.WordTrace]
  refine ⟨139744753753285764352620301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186326338337714352470160401 139744753753285764352620301)
  ·
    refine ⟨52404282657482161632232613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139744753753285764352620301 52404282657482161632232613)
    ·
      refine ⟨9825802998277905306043615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52404282657482161632232613 9825802998277905306043615)
      ·
        refine ⟨14738704497416857959065423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9825802998277905306043615 14738704497416857959065423)
        ·
          refine ⟨22108056746125286938598135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14738704497416857959065423 22108056746125286938598135)
          ·
            refine ⟨33162085119187930407897203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22108056746125286938598135 33162085119187930407897203)
            ·
              refine ⟨49743127678781895611845805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33162085119187930407897203 49743127678781895611845805)
              ·
                refine ⟨18653672879543210854442177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49743127678781895611845805 18653672879543210854442177)
                ·
                  refine ⟨13990254659657408140831633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18653672879543210854442177 13990254659657408140831633)
                  ·
                    refine ⟨10492690994743056105623725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13990254659657408140831633 10492690994743056105623725)
                    ·
                      refine ⟨3934759123028646039608897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10492690994743056105623725 3934759123028646039608897)
                      ·
                        rfl

theorem cell23_7662916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_7662916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662916 prefixEnd_7662916 := by exact prefixLift 7662916
  have htrace : WordTrace (prefixWord ++ tailWord_7662916) baseStart_7662916 baseEnd_7662916 := by
    simpa [prefixWord, tailWord_7662916, baseEnd_7662916] using wordTrace_append hprefix tailTrace_7662916
  have hstable : (prefixWord ++ tailWord_7662916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662916).length < 2 ^ (prefixWord ++ tailWord_7662916).sum := by decide
  have hdescent : baseEnd_7662916 < baseStart_7662916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662946 : List Nat := [3, 3, 2, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_7662946 : Nat := 118140960795 + 7662946 * 2 ^ 59
def prefixEnd_7662946 : Nat := 4983230072969 + 3 ^ 40 * 7662946 * 2
def baseEnd_7662946 : Nat := 3934774527448280922233759

theorem tailTrace_7662946 : CollatzResearch.WordTrace tailWord_7662946 prefixEnd_7662946 3934774527448280922233759 := by
  unfold tailWord_7662946
  simp only [CollatzResearch.WordTrace]
  refine ⟨69872650424115710957208173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186327067797641895885888461 69872650424115710957208173)
  ·
    refine ⟨26202243909043391608953065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69872650424115710957208173 26202243909043391608953065)
    ·
      refine ⟨19651682931782543706714799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26202243909043391608953065 19651682931782543706714799)
      ·
        refine ⟨29477524397673815560072199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19651682931782543706714799 29477524397673815560072199)
        ·
          refine ⟨44216286596510723340108299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29477524397673815560072199 44216286596510723340108299)
          ·
            refine ⟨66324429894766085010162449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44216286596510723340108299 66324429894766085010162449)
            ·
              refine ⟨49743322421074563757621837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66324429894766085010162449 49743322421074563757621837)
              ·
                refine ⟨18653745907902961409108189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49743322421074563757621837 18653745907902961409108189)
                ·
                  refine ⟨6995154715463610528415571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18653745907902961409108189 6995154715463610528415571)
                  ·
                    refine ⟨10492732073195415792623357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6995154715463610528415571 10492732073195415792623357)
                    ·
                      refine ⟨3934774527448280922233759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10492732073195415792623357 3934774527448280922233759)
                      ·
                        rfl

theorem cell23_7662946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_7662946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662946 prefixEnd_7662946 := by exact prefixLift 7662946
  have htrace : WordTrace (prefixWord ++ tailWord_7662946) baseStart_7662946 baseEnd_7662946 := by
    simpa [prefixWord, tailWord_7662946, baseEnd_7662946] using wordTrace_append hprefix tailTrace_7662946
  have hstable : (prefixWord ++ tailWord_7662946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662946).length < 2 ^ (prefixWord ++ tailWord_7662946).sum := by decide
  have hdescent : baseEnd_7662946 < baseStart_7662946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7662996 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_7662996 : Nat := 118140960795 + 7662996 * 2 ^ 59
def prefixEnd_7662996 : Nat := 4983230072969 + 3 ^ 40 * 7662996 * 2
def baseEnd_7662996 : Nat := 1311600067160335242202843

theorem tailTrace_7662996 : CollatzResearch.WordTrace tailWord_7662996 prefixEnd_7662996 1311600067160335242202843 := by
  unfold tailWord_7662996
  simp only [CollatzResearch.WordTrace]
  refine ⟨139746212673140851184076421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186328283564187801578768561 139746212673140851184076421)
  ·
    refine ⟨26202414876213909597014329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139746212673140851184076421 26202414876213909597014329)
    ·
      refine ⟨19651811157160432197760747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26202414876213909597014329 19651811157160432197760747)
      ·
        refine ⟨29477716735740648296641121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19651811157160432197760747 29477716735740648296641121)
        ·
          refine ⟨22108287551805486222480841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29477716735740648296641121 22108287551805486222480841)
          ·
            refine ⟨16581215663854114666860631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22108287551805486222480841 16581215663854114666860631)
            ·
              refine ⟨24871823495781172000290947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16581215663854114666860631 24871823495781172000290947)
              ·
                refine ⟨37307735243671758000436421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24871823495781172000290947 37307735243671758000436421)
                ·
                  refine ⟨6995200358188454625081829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37307735243671758000436421 6995200358188454625081829)
                  ·
                    refine ⟨1311600067160335242202843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6995200358188454625081829 1311600067160335242202843)
                    ·
                      rfl

theorem cell23_7662996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_7662996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7662996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7662996 prefixEnd_7662996 := by exact prefixLift 7662996
  have htrace : WordTrace (prefixWord ++ tailWord_7662996) baseStart_7662996 baseEnd_7662996 := by
    simpa [prefixWord, tailWord_7662996, baseEnd_7662996] using wordTrace_append hprefix tailTrace_7662996
  have hstable : (prefixWord ++ tailWord_7662996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7662996).length < 2 ^ (prefixWord ++ tailWord_7662996).sum := by decide
  have hdescent : baseEnd_7662996 < baseStart_7662996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7662996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663016 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_7663016 : Nat := 118140960795 + 7663016 * 2 ^ 59
def prefixEnd_7663016 : Nat := 4983230072969 + 3 ^ 40 * 7663016 * 2
def baseEnd_7663016 : Nat := 3934810471094095648358437

theorem tailTrace_7663016 : CollatzResearch.WordTrace tailWord_7663016 prefixEnd_7663016 3934810471094095648358437 := by
  unfold tailWord_7663016
  simp only [CollatzResearch.WordTrace]
  refine ⟨139746577403104622891940451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186328769870806163855920601 139746577403104622891940451)
  ·
    refine ⟨209619866104656934337910677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139746577403104622891940451 209619866104656934337910677)
    ·
      refine ⟨9825931223655793797089563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 209619866104656934337910677 9825931223655793797089563)
      ·
        refine ⟨14738896835483690695634345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9825931223655793797089563 14738896835483690695634345)
        ·
          refine ⟨11054172626612768021725759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14738896835483690695634345 11054172626612768021725759)
          ·
            refine ⟨16581258939919152032588639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11054172626612768021725759 16581258939919152032588639)
            ·
              refine ⟨24871888409878728048882959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16581258939919152032588639 24871888409878728048882959)
              ·
                refine ⟨37307832614818092073324439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24871888409878728048882959 37307832614818092073324439)
                ·
                  refine ⟨55961748922227138109986659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37307832614818092073324439 55961748922227138109986659)
                  ·
                    refine ⟨83942623383340707164979989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55961748922227138109986659 83942623383340707164979989)
                    ·
                      refine ⟨3934810471094095648358437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83942623383340707164979989 3934810471094095648358437)
                      ·
                        rfl

theorem cell23_7663016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_7663016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663016 prefixEnd_7663016 := by exact prefixLift 7663016
  have htrace : WordTrace (prefixWord ++ tailWord_7663016) baseStart_7663016 baseEnd_7663016 := by
    simpa [prefixWord, tailWord_7663016, baseEnd_7663016] using wordTrace_append hprefix tailTrace_7663016
  have hstable : (prefixWord ++ tailWord_7663016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663016).length < 2 ^ (prefixWord ++ tailWord_7663016).sum := by decide
  have hdescent : baseEnd_7663016 < baseStart_7663016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663032 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 2, 2, 5]
def baseStart_7663032 : Nat := 118140960795 + 7663032 * 2 ^ 59
def prefixEnd_7663032 : Nat := 4983230072969 + 3 ^ 40 * 7663032 * 2
def baseEnd_7663032 : Nat := 3934818686784567585758363

theorem tailTrace_7663032 : CollatzResearch.WordTrace tailWord_7663032 prefixEnd_7663032 3934818686784567585758363 := by
  unfold tailWord_7663032
  simp only [CollatzResearch.WordTrace]
  refine ⟨139746869187075640258231675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186329158916100853677642233 139746869187075640258231675)
  ·
    refine ⟨209620303780613460387347513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139746869187075640258231675 209620303780613460387347513)
    ·
      refine ⟨157215227835460095290510635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209620303780613460387347513 157215227835460095290510635)
      ·
        refine ⟨235822841753190142935765953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157215227835460095290510635 235822841753190142935765953)
        ·
          refine ⟨176867131314892607201824465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235822841753190142935765953 176867131314892607201824465)
          ·
            refine ⟨132650348486169455401368349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176867131314892607201824465 132650348486169455401368349)
            ·
              refine ⟨49743880682313545775513131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132650348486169455401368349 49743880682313545775513131)
              ·
                refine ⟨74615821023470318663269697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49743880682313545775513131 74615821023470318663269697)
                ·
                  refine ⟨55961865767602738997452273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74615821023470318663269697 55961865767602738997452273)
                  ·
                    refine ⟨41971399325702054248089205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55961865767602738997452273 41971399325702054248089205)
                    ·
                      refine ⟨3934818686784567585758363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41971399325702054248089205 3934818686784567585758363)
                      ·
                        rfl

theorem cell23_7663032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_7663032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663032 prefixEnd_7663032 := by exact prefixLift 7663032
  have htrace : WordTrace (prefixWord ++ tailWord_7663032) baseStart_7663032 baseEnd_7663032 := by
    simpa [prefixWord, tailWord_7663032, baseEnd_7663032] using wordTrace_append hprefix tailTrace_7663032
  have hstable : (prefixWord ++ tailWord_7663032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663032).length < 2 ^ (prefixWord ++ tailWord_7663032).sum := by decide
  have hdescent : baseEnd_7663032 < baseStart_7663032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663079 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_7663079 : Nat := 118140960795 + 7663079 * 2 ^ 59
def prefixEnd_7663079 : Nat := 4983230072969 + 3 ^ 40 * 7663079 * 2
def baseEnd_7663079 : Nat := 3934842820375328901870647

theorem tailTrace_7663079 : CollatzResearch.WordTrace tailWord_7663079 prefixEnd_7663079 3934842820375328901870647 := by
  unfold tailWord_7663079
  simp only [CollatzResearch.WordTrace]
  refine ⟨279495452604981007543424291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186330301736654005028949527 279495452604981007543424291)
  ·
    refine ⟨419243178907471511315136437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279495452604981007543424291 419243178907471511315136437)
    ·
      refine ⟨39304048022575454185794041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 419243178907471511315136437 39304048022575454185794041)
      ·
        refine ⟨29478036016931590639345531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39304048022575454185794041 29478036016931590639345531)
        ·
          refine ⟨44217054025397385959018297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29478036016931590639345531 44217054025397385959018297)
          ·
            refine ⟨33162790519048039469263723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44217054025397385959018297 33162790519048039469263723)
            ·
              refine ⟨49744185778572059203895585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33162790519048039469263723 49744185778572059203895585)
              ·
                refine ⟨37308139333929044402921689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49744185778572059203895585 37308139333929044402921689)
                ·
                  refine ⟨27981104500446783302191267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37308139333929044402921689 27981104500446783302191267)
                  ·
                    refine ⟨41971656750670174953286901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27981104500446783302191267 41971656750670174953286901)
                    ·
                      refine ⟨3934842820375328901870647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41971656750670174953286901 3934842820375328901870647)
                      ·
                        rfl

theorem cell23_7663079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_7663079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663079 prefixEnd_7663079 := by exact prefixLift 7663079
  have htrace : WordTrace (prefixWord ++ tailWord_7663079) baseStart_7663079 baseEnd_7663079 := by
    simpa [prefixWord, tailWord_7663079, baseEnd_7663079] using wordTrace_append hprefix tailTrace_7663079
  have hstable : (prefixWord ++ tailWord_7663079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663079).length < 2 ^ (prefixWord ++ tailWord_7663079).sum := by decide
  have hdescent : baseEnd_7663079 < baseStart_7663079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663093 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_7663093 : Nat := 118140960795 + 7663093 * 2 ^ 59
def prefixEnd_7663093 : Nat := 4983230072969 + 3 ^ 40 * 7663093 * 2
def baseEnd_7663093 : Nat := 3934850009104491847095583

theorem tailTrace_7663093 : CollatzResearch.WordTrace tailWord_7663093 prefixEnd_7663093 3934850009104491847095583 := by
  unfold tailWord_7663093
  simp only [CollatzResearch.WordTrace]
  refine ⟨279495963226930287934433933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186330642151286858622955955 279495963226930287934433933)
  ·
    refine ⟨104810986210098857975412725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279495963226930287934433933 104810986210098857975412725)
    ·
      refine ⟨9826029957196767935194943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104810986210098857975412725 9826029957196767935194943)
      ·
        refine ⟨14739044935795151902792415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9826029957196767935194943 14739044935795151902792415)
        ·
          refine ⟨22108567403692727854188623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14739044935795151902792415 22108567403692727854188623)
          ·
            refine ⟨33162851105539091781282935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22108567403692727854188623 33162851105539091781282935)
            ·
              refine ⟨49744276658308637671924403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33162851105539091781282935 49744276658308637671924403)
              ·
                refine ⟨74616414987462956507886605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49744276658308637671924403 74616414987462956507886605)
                ·
                  refine ⟨27981155620298608690457477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74616414987462956507886605 27981155620298608690457477)
                  ·
                    refine ⟨5246466678805989129460777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27981155620298608690457477 5246466678805989129460777)
                    ·
                      refine ⟨3934850009104491847095583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5246466678805989129460777 3934850009104491847095583)
                      ·
                        rfl

theorem cell23_7663093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_7663093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663093 prefixEnd_7663093 := by exact prefixLift 7663093
  have htrace : WordTrace (prefixWord ++ tailWord_7663093) baseStart_7663093 baseEnd_7663093 := by
    simpa [prefixWord, tailWord_7663093, baseEnd_7663093] using wordTrace_append hprefix tailTrace_7663093
  have hstable : (prefixWord ++ tailWord_7663093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663093).length < 2 ^ (prefixWord ++ tailWord_7663093).sum := by decide
  have hdescent : baseEnd_7663093 < baseStart_7663093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663109 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 2, 3, 3]
def baseStart_7663109 : Nat := 118140960795 + 7663109 * 2 ^ 59
def prefixEnd_7663109 : Nat := 4983230072969 + 3 ^ 40 * 7663109 * 2
def baseEnd_7663109 : Nat := 3934858224794963784495509

theorem tailTrace_7663109 : CollatzResearch.WordTrace tailWord_7663109 prefixEnd_7663109 3934858224794963784495509 := by
  unfold tailWord_7663109
  simp only [CollatzResearch.WordTrace]
  refine ⟨279496546794872322667016381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186331031196581548444677587 279496546794872322667016381)
  ·
    refine ⟨104811205048077121000131143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279496546794872322667016381 104811205048077121000131143)
    ·
      refine ⟨157216807572115681500196715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104811205048077121000131143 157216807572115681500196715)
      ·
        refine ⟨235825211358173522250295073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157216807572115681500196715 235825211358173522250295073)
        ·
          refine ⟨176868908518630141687721305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235825211358173522250295073 176868908518630141687721305)
          ·
            refine ⟨132651681388972606265790979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176868908518630141687721305 132651681388972606265790979)
            ·
              refine ⟨198977522083458909398686469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132651681388972606265790979 198977522083458909398686469)
              ·
                refine ⟨37308285390648545512253713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198977522083458909398686469 37308285390648545512253713)
                ·
                  refine ⟨27981214042986409134190285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37308285390648545512253713 27981214042986409134190285)
                  ·
                    refine ⟨10492955266119903425321357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27981214042986409134190285 10492955266119903425321357)
                    ·
                      refine ⟨3934858224794963784495509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10492955266119903425321357 3934858224794963784495509)
                      ·
                        rfl

theorem cell23_7663109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_7663109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663109 prefixEnd_7663109 := by exact prefixLift 7663109
  have htrace : WordTrace (prefixWord ++ tailWord_7663109) baseStart_7663109 baseEnd_7663109 := by
    simpa [prefixWord, tailWord_7663109, baseEnd_7663109] using wordTrace_append hprefix tailTrace_7663109
  have hstable : (prefixWord ++ tailWord_7663109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663109).length < 2 ^ (prefixWord ++ tailWord_7663109).sum := by decide
  have hdescent : baseEnd_7663109 < baseStart_7663109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663186 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_7663186 : Nat := 118140960795 + 7663186 * 2 ^ 59
def prefixEnd_7663186 : Nat := 4983230072969 + 3 ^ 40 * 7663186 * 2
def baseEnd_7663186 : Nat := 3934897762805359983232655

theorem tailTrace_7663186 : CollatzResearch.WordTrace tailWord_7663186 prefixEnd_7663186 3934897762805359983232655 := by
  unfold tailWord_7663186
  simp only [CollatzResearch.WordTrace]
  refine ⟨69874838803898341204392353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186332903477062243211712941 69874838803898341204392353)
  ·
    refine ⟨52406129102923755903294265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69874838803898341204392353 52406129102923755903294265)
    ·
      refine ⟨39304596827192816927470699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52406129102923755903294265 39304596827192816927470699)
      ·
        refine ⟨58956895240789225391206049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39304596827192816927470699 58956895240789225391206049)
        ·
          refine ⟨44217671430591919043404537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58956895240789225391206049 44217671430591919043404537)
          ·
            refine ⟨33163253572943939282553403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44217671430591919043404537 33163253572943939282553403)
            ·
              refine ⟨49744880359415908923830105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33163253572943939282553403 49744880359415908923830105)
              ·
                refine ⟨37308660269561931692872579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49744880359415908923830105 37308660269561931692872579)
                ·
                  refine ⟨55962990404342897539308869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37308660269561931692872579 55962990404342897539308869)
                  ·
                    refine ⟨10493060700814293288620413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55962990404342897539308869 10493060700814293288620413)
                    ·
                      refine ⟨3934897762805359983232655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10493060700814293288620413 3934897762805359983232655)
                      ·
                        rfl

theorem cell23_7663186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_7663186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663186 prefixEnd_7663186 := by exact prefixLift 7663186
  have htrace : WordTrace (prefixWord ++ tailWord_7663186) baseStart_7663186 baseEnd_7663186 := by
    simpa [prefixWord, tailWord_7663186, baseEnd_7663186] using wordTrace_append hprefix tailTrace_7663186
  have hstable : (prefixWord ++ tailWord_7663186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663186).length < 2 ^ (prefixWord ++ tailWord_7663186).sum := by decide
  have hdescent : baseEnd_7663186 < baseStart_7663186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663210 : List Nat := [3, 1, 3, 2, 1, 2, 3, 3, 1, 4]
def baseStart_7663210 : Nat := 118140960795 + 7663210 * 2 ^ 59
def prefixEnd_7663210 : Nat := 4983230072969 + 3 ^ 40 * 7663210 * 2
def baseEnd_7663210 : Nat := 1311636695447022629777515

theorem tailTrace_7663210 : CollatzResearch.WordTrace tailWord_7663210 prefixEnd_7663210 1311636695447022629777515 := by
  unfold tailWord_7663210
  simp only [CollatzResearch.WordTrace]
  refine ⟨69875057641876604229110771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186333487045004277944295389 69875057641876604229110771)
  ·
    refine ⟨104812586462814906343666157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69875057641876604229110771 104812586462814906343666157)
    ·
      refine ⟨39304719923555589878874809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104812586462814906343666157 39304719923555589878874809)
      ·
        refine ⟨29478539942666692409156107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39304719923555589878874809 29478539942666692409156107)
        ·
          refine ⟨44217809914000038613734161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29478539942666692409156107 44217809914000038613734161)
          ·
            refine ⟨33163357435500028960300621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44217809914000038613734161 33163357435500028960300621)
            ·
              refine ⟨12436259038312510860112733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33163357435500028960300621 12436259038312510860112733)
              ·
                refine ⟨4663597139367191572542275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12436259038312510860112733 4663597139367191572542275)
                ·
                  refine ⟨6995395709050787358813413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4663597139367191572542275 6995395709050787358813413)
                  ·
                    refine ⟨1311636695447022629777515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6995395709050787358813413 1311636695447022629777515)
                    ·
                      rfl

theorem cell23_7663210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_7663210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663210 prefixEnd_7663210 := by exact prefixLift 7663210
  have htrace : WordTrace (prefixWord ++ tailWord_7663210) baseStart_7663210 baseEnd_7663210 := by
    simpa [prefixWord, tailWord_7663210, baseEnd_7663210] using wordTrace_append hprefix tailTrace_7663210
  have hstable : (prefixWord ++ tailWord_7663210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663210).length < 2 ^ (prefixWord ++ tailWord_7663210).sum := by decide
  have hdescent : baseEnd_7663210 < baseStart_7663210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663226 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2]
def baseStart_7663226 : Nat := 118140960795 + 7663226 * 2 ^ 59
def prefixEnd_7663226 : Nat := 4983230072969 + 3 ^ 40 * 7663226 * 2
def baseEnd_7663226 : Nat := 3934918302031539826732471

theorem tailTrace_7663226 : CollatzResearch.WordTrace tailWord_7663226 prefixEnd_7663226 3934918302031539826732471 := by
  unfold tailWord_7663226
  simp only [CollatzResearch.WordTrace]
  refine ⟨69875203533862112912256383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186333876090298967766017021 69875203533862112912256383)
  ·
    refine ⟨104812805300793169368384575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69875203533862112912256383 104812805300793169368384575)
    ·
      refine ⟨157219207951189754052576863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104812805300793169368384575 157219207951189754052576863)
      ·
        refine ⟨235828811926784631078865295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157219207951189754052576863 235828811926784631078865295)
        ·
          refine ⟨353743217890176946618297943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235828811926784631078865295 353743217890176946618297943)
          ·
            refine ⟨530614826835265419927446915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353743217890176946618297943 530614826835265419927446915)
            ·
              refine ⟨795922240252898129891170373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530614826835265419927446915 795922240252898129891170373)
              ·
                refine ⟨149235420047418399354594445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 795922240252898129891170373 149235420047418399354594445)
                ·
                  refine ⟨55963282517781899757972917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149235420047418399354594445 55963282517781899757972917)
                  ·
                    refine ⟨5246557736042053102309961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55963282517781899757972917 5246557736042053102309961)
                    ·
                      refine ⟨3934918302031539826732471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5246557736042053102309961 3934918302031539826732471)
                      ·
                        rfl

theorem cell23_7663226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2].length) (baseStart_7663226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663226 prefixEnd_7663226 := by exact prefixLift 7663226
  have htrace : WordTrace (prefixWord ++ tailWord_7663226) baseStart_7663226 baseEnd_7663226 := by
    simpa [prefixWord, tailWord_7663226, baseEnd_7663226] using wordTrace_append hprefix tailTrace_7663226
  have hstable : (prefixWord ++ tailWord_7663226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663226).length < 2 ^ (prefixWord ++ tailWord_7663226).sum := by decide
  have hdescent : baseEnd_7663226 < baseStart_7663226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663283 : List Nat := [1, 1, 1, 2, 3, 3, 4, 2, 2, 4]
def baseStart_7663283 : Nat := 118140960795 + 7663283 * 2 ^ 59
def prefixEnd_7663283 : Nat := 4983230072969 + 3 ^ 40 * 7663283 * 2
def baseEnd_7663283 : Nat := 1311649190142948701239903

theorem tailTrace_7663283 : CollatzResearch.WordTrace tailWord_7663283 prefixEnd_7663283 1311649190142948701239903 := by
  unfold tailWord_7663283
  simp only [CollatzResearch.WordTrace]
  refine ⟨279502893096241950383850503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186335262064161300255900335 279502893096241950383850503)
  ·
    refine ⟨419254339644362925575775755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279502893096241950383850503 419254339644362925575775755)
    ·
      refine ⟨628881509466544388363663633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419254339644362925575775755 628881509466544388363663633)
      ·
        refine ⟨471661132099908291272747725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628881509466544388363663633 471661132099908291272747725)
        ·
          refine ⟨176872924537465609227280397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 471661132099908291272747725 176872924537465609227280397)
          ·
            refine ⟨66327346701549603460230149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176872924537465609227280397 66327346701549603460230149)
            ·
              refine ⟨12436377506540550648793153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66327346701549603460230149 12436377506540550648793153)
              ·
                refine ⟨9327283129905412986594865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12436377506540550648793153 9327283129905412986594865)
                ·
                  refine ⟨6995462347429059739946149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9327283129905412986594865 6995462347429059739946149)
                  ·
                    refine ⟨1311649190142948701239903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6995462347429059739946149 1311649190142948701239903)
                    ·
                      rfl

theorem cell23_7663283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 4].length) (baseStart_7663283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663283 prefixEnd_7663283 := by exact prefixLift 7663283
  have htrace : WordTrace (prefixWord ++ tailWord_7663283) baseStart_7663283 baseEnd_7663283 := by
    simpa [prefixWord, tailWord_7663283, baseEnd_7663283] using wordTrace_append hprefix tailTrace_7663283
  have hstable : (prefixWord ++ tailWord_7663283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663283).length < 2 ^ (prefixWord ++ tailWord_7663283).sum := by decide
  have hdescent : baseEnd_7663283 < baseStart_7663283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663324 : List Nat := [2, 2, 5, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_7663324 : Nat := 118140960795 + 7663324 * 2 ^ 59
def prefixEnd_7663324 : Nat := 4983230072969 + 3 ^ 40 * 7663324 * 2
def baseEnd_7663324 : Nat := 3934968623135680443307021

theorem tailTrace_7663324 : CollatzResearch.WordTrace tailWord_7663324 prefixEnd_7663324 3934968623135680443307021 := by
  unfold tailWord_7663324
  simp only [CollatzResearch.WordTrace]
  refine ⟨139752194244546707193046513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186336258992728942924062017 139752194244546707193046513)
  ·
    refine ⟨104814145683410030394784885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139752194244546707193046513 104814145683410030394784885)
    ·
      refine ⟨9826326157819690349511083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104814145683410030394784885 9826326157819690349511083)
      ·
        refine ⟨14739489236729535524266625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9826326157819690349511083 14739489236729535524266625)
        ·
          refine ⟨11054616927547151643199969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14739489236729535524266625 11054616927547151643199969)
          ·
            refine ⟨8290962695660363732399977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11054616927547151643199969 8290962695660363732399977)
            ·
              refine ⟨6218222021745272799299983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8290962695660363732399977 6218222021745272799299983)
              ·
                refine ⟨9327333032617909198949975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6218222021745272799299983 9327333032617909198949975)
                ·
                  refine ⟨13990999548926863798424963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9327333032617909198949975 13990999548926863798424963)
                  ·
                    refine ⟨20986499323390295697637445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13990999548926863798424963 20986499323390295697637445)
                    ·
                      refine ⟨3934968623135680443307021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20986499323390295697637445 3934968623135680443307021)
                      ·
                        rfl

theorem cell23_7663324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_7663324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663324 prefixEnd_7663324 := by exact prefixLift 7663324
  have htrace : WordTrace (prefixWord ++ tailWord_7663324) baseStart_7663324 baseEnd_7663324 := by
    simpa [prefixWord, tailWord_7663324, baseEnd_7663324] using wordTrace_append hprefix tailTrace_7663324
  have hstable : (prefixWord ++ tailWord_7663324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663324).length < 2 ^ (prefixWord ++ tailWord_7663324).sum := by decide
  have hdescent : baseEnd_7663324 < baseStart_7663324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663340 : List Nat := [2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 3]
def baseStart_7663340 : Nat := 118140960795 + 7663340 * 2 ^ 59
def prefixEnd_7663340 : Nat := 4983230072969 + 3 ^ 40 * 7663340 * 2
def baseEnd_7663340 : Nat := 3934976838826152380706947

theorem tailTrace_7663340 : CollatzResearch.WordTrace tailWord_7663340 prefixEnd_7663340 3934976838826152380706947 := by
  unfold tailWord_7663340
  simp only [CollatzResearch.WordTrace]
  refine ⟨139752486028517724559337737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186336648038023632745783649 139752486028517724559337737)
  ·
    refine ⟨104814364521388293419503303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139752486028517724559337737 104814364521388293419503303)
    ·
      refine ⟨157221546782082440129254955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104814364521388293419503303 157221546782082440129254955)
      ·
        refine ⟨235832320173123660193882433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157221546782082440129254955 235832320173123660193882433)
        ·
          refine ⟨176874240129842745145411825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235832320173123660193882433 176874240129842745145411825)
          ·
            refine ⟨132655680097382058859058869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176874240129842745145411825 132655680097382058859058869)
            ·
              refine ⟨12436470009129568018036769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132655680097382058859058869 12436470009129568018036769)
              ·
                refine ⟨9327352506847176013527577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12436470009129568018036769 9327352506847176013527577)
                ·
                  refine ⟨6995514380135382010145683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9327352506847176013527577 6995514380135382010145683)
                  ·
                    refine ⟨10493271570203073015218525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6995514380135382010145683 10493271570203073015218525)
                    ·
                      refine ⟨3934976838826152380706947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10493271570203073015218525 3934976838826152380706947)
                      ·
                        rfl

theorem cell23_7663340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 3].length) (baseStart_7663340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663340 prefixEnd_7663340 := by exact prefixLift 7663340
  have htrace : WordTrace (prefixWord ++ tailWord_7663340) baseStart_7663340 baseEnd_7663340 := by
    simpa [prefixWord, tailWord_7663340, baseEnd_7663340] using wordTrace_append hprefix tailTrace_7663340
  have hstable : (prefixWord ++ tailWord_7663340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663340).length < 2 ^ (prefixWord ++ tailWord_7663340).sum := by decide
  have hdescent : baseEnd_7663340 < baseStart_7663340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663356 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 2, 6]
def baseStart_7663356 : Nat := 118140960795 + 7663356 * 2 ^ 59
def prefixEnd_7663356 : Nat := 4983230072969 + 3 ^ 40 * 7663356 * 2
def baseEnd_7663356 : Nat := 1311661684838874772702291

theorem tailTrace_7663356 : CollatzResearch.WordTrace tailWord_7663356 prefixEnd_7663356 1311661684838874772702291 := by
  unfold tailWord_7663356
  simp only [CollatzResearch.WordTrace]
  refine ⟨139752777812488741925628961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186337037083318322567505281 139752777812488741925628961)
  ·
    refine ⟨104814583359366556444221721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139752777812488741925628961 104814583359366556444221721)
    ·
      refine ⟨78610937519524917333166291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104814583359366556444221721 78610937519524917333166291)
      ·
        refine ⟨117916406279287375999749437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78610937519524917333166291 117916406279287375999749437)
        ·
          refine ⟨44218652354732765999906039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117916406279287375999749437 44218652354732765999906039)
          ·
            refine ⟨66327978532099148999859059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44218652354732765999906039 66327978532099148999859059)
            ·
              refine ⟨99491967798148723499788589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66327978532099148999859059 99491967798148723499788589)
              ·
                refine ⟨37309487924305771312420721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99491967798148723499788589 37309487924305771312420721)
                ·
                  refine ⟨27982115943229328484315541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37309487924305771312420721 27982115943229328484315541)
                  ·
                    refine ⟨1311661684838874772702291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27982115943229328484315541 1311661684838874772702291)
                    ·
                      rfl

theorem cell23_7663356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_7663356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663356 prefixEnd_7663356 := by exact prefixLift 7663356
  have htrace : WordTrace (prefixWord ++ tailWord_7663356) baseStart_7663356 baseEnd_7663356 := by
    simpa [prefixWord, tailWord_7663356, baseEnd_7663356] using wordTrace_append hprefix tailTrace_7663356
  have hstable : (prefixWord ++ tailWord_7663356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663356).length < 2 ^ (prefixWord ++ tailWord_7663356).sum := by decide
  have hdescent : baseEnd_7663356 < baseStart_7663356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663383 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 5]
def baseStart_7663383 : Nat := 118140960795 + 7663383 * 2 ^ 59
def prefixEnd_7663383 : Nat := 4983230072969 + 3 ^ 40 * 7663383 * 2
def baseEnd_7663383 : Nat := 3934998918494295712469249

theorem tailTrace_7663383 : CollatzResearch.WordTrace tailWord_7663383 prefixEnd_7663383 3934998918494295712469249 := by
  unfold tailWord_7663383
  simp only [CollatzResearch.WordTrace]
  refine ⟨279506540395879667462490803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186337693597253111641660535 279506540395879667462490803)
  ·
    refine ⟨419259810593819501193736205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279506540395879667462490803 419259810593819501193736205)
    ·
      refine ⟨157222428972682312947651077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419259810593819501193736205 157222428972682312947651077)
      ·
        refine ⟨29479205432377933677684577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157222428972682312947651077 29479205432377933677684577)
        ·
          refine ⟨22109404074283450258263433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29479205432377933677684577 22109404074283450258263433)
          ·
            refine ⟨16582053055712587693697575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22109404074283450258263433 16582053055712587693697575)
            ·
              refine ⟨24873079583568881540546363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16582053055712587693697575 24873079583568881540546363)
              ·
                refine ⟨37309619375353322310819545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24873079583568881540546363 37309619375353322310819545)
                ·
                  refine ⟨27982214531514991733114659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37309619375353322310819545 27982214531514991733114659)
                  ·
                    refine ⟨41973321797272487599671989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27982214531514991733114659 41973321797272487599671989)
                    ·
                      refine ⟨3934998918494295712469249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41973321797272487599671989 3934998918494295712469249)
                      ·
                        rfl

theorem cell23_7663383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_7663383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663383 prefixEnd_7663383 := by exact prefixLift 7663383
  have htrace : WordTrace (prefixWord ++ tailWord_7663383) baseStart_7663383 baseEnd_7663383 := by
    simpa [prefixWord, tailWord_7663383, baseEnd_7663383] using wordTrace_append hprefix tailTrace_7663383
  have hstable : (prefixWord ++ tailWord_7663383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663383).length < 2 ^ (prefixWord ++ tailWord_7663383).sum := by decide
  have hdescent : baseEnd_7663383 < baseStart_7663383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663433 : List Nat := [1, 2, 1, 1, 2, 4, 4, 1, 2, 5]
def baseStart_7663433 : Nat := 118140960795 + 7663433 * 2 ^ 59
def prefixEnd_7663433 : Nat := 4983230072969 + 3 ^ 40 * 7663433 * 2
def baseEnd_7663433 : Nat := 1311674864175673505614673

theorem tailTrace_7663433 : CollatzResearch.WordTrace tailWord_7663433 prefixEnd_7663433 1311674864175673505614673 := by
  unfold tailWord_7663433
  simp only [CollatzResearch.WordTrace]
  refine ⟨279508364045698526001810953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186338909363799017334540635 279508364045698526001810953)
  ·
    refine ⟨209631273034273894501358215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279508364045698526001810953 209631273034273894501358215)
    ·
      refine ⟨314446909551410841752037323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209631273034273894501358215 314446909551410841752037323)
      ·
        refine ⟨471670364327116262628055985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314446909551410841752037323 471670364327116262628055985)
        ·
          refine ⟨353752773245337196971041989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471670364327116262628055985 353752773245337196971041989)
          ·
            refine ⟨66328644983500724432070373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 353752773245337196971041989 66328644983500724432070373)
            ·
              refine ⟨12436620934406385831013195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66328644983500724432070373 12436620934406385831013195)
              ·
                refine ⟨18654931401609578746519793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12436620934406385831013195 18654931401609578746519793)
                ·
                  refine ⟨13991198551207184059889845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18654931401609578746519793 13991198551207184059889845)
                  ·
                    refine ⟨1311674864175673505614673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13991198551207184059889845 1311674864175673505614673)
                    ·
                      rfl

theorem cell23_7663433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 5].length) (baseStart_7663433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663433 prefixEnd_7663433 := by exact prefixLift 7663433
  have htrace : WordTrace (prefixWord ++ tailWord_7663433) baseStart_7663433 baseEnd_7663433 := by
    simpa [prefixWord, tailWord_7663433, baseEnd_7663433] using wordTrace_append hprefix tailTrace_7663433
  have hstable : (prefixWord ++ tailWord_7663433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663433).length < 2 ^ (prefixWord ++ tailWord_7663433).sum := by decide
  have hdescent : baseEnd_7663433 < baseStart_7663433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663473 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 1, 4, 3]
def baseStart_7663473 : Nat := 118140960795 + 7663473 * 2 ^ 59
def prefixEnd_7663473 : Nat := 4983230072969 + 3 ^ 40 * 7663473 * 2
def baseEnd_7663473 : Nat := 3935045131753200360343835

theorem tailTrace_7663473 : CollatzResearch.WordTrace tailWord_7663473 prefixEnd_7663473 3935045131753200360343835 := by
  unfold tailWord_7663473
  simp only [CollatzResearch.WordTrace]
  refine ⟨279509822965553612833267073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186339881977035741888844715 279509822965553612833267073)
  ·
    refine ⟨209632367224165209624950305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279509822965553612833267073 209632367224165209624950305)
    ·
      refine ⟨157224275418123907218712729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209632367224165209624950305 157224275418123907218712729)
      ·
        refine ⟨117918206563592930414034547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157224275418123907218712729 117918206563592930414034547)
        ·
          refine ⟨176877309845389395621051821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117918206563592930414034547 176877309845389395621051821)
          ·
            refine ⟨66328991192021023357894433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176877309845389395621051821 66328991192021023357894433)
            ·
              refine ⟨49746743394015767518420825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66328991192021023357894433 49746743394015767518420825)
              ·
                refine ⟨37310057545511825638815619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49746743394015767518420825 37310057545511825638815619)
                ·
                  refine ⟨55965086318267738458223429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37310057545511825638815619 55965086318267738458223429)
                  ·
                    refine ⟨10493453684675200960916893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55965086318267738458223429 10493453684675200960916893)
                    ·
                      refine ⟨3935045131753200360343835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10493453684675200960916893 3935045131753200360343835)
                      ·
                        rfl

theorem cell23_7663473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_7663473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663473 prefixEnd_7663473 := by exact prefixLift 7663473
  have htrace : WordTrace (prefixWord ++ tailWord_7663473) baseStart_7663473 baseEnd_7663473 := by
    simpa [prefixWord, tailWord_7663473, baseEnd_7663473] using wordTrace_append hprefix tailTrace_7663473
  have hstable : (prefixWord ++ tailWord_7663473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663473).length < 2 ^ (prefixWord ++ tailWord_7663473).sum := by decide
  have hdescent : baseEnd_7663473 < baseStart_7663473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663497 : List Nat := [1, 2, 1, 1, 5, 1, 4, 3, 1, 4]
def baseStart_7663497 : Nat := 118140960795 + 7663497 * 2 ^ 59
def prefixEnd_7663497 : Nat := 4983230072969 + 3 ^ 40 * 7663497 * 2
def baseEnd_7663497 : Nat := 1311685818429636088814575

theorem tailTrace_7663497 : CollatzResearch.WordTrace tailWord_7663497 prefixEnd_7663497 1311685818429636088814575 := by
  unfold tailWord_7663497
  simp only [CollatzResearch.WordTrace]
  refine ⟨279510698317466664932140745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186340465544977776621427163 279510698317466664932140745)
  ·
    refine ⟨209633023738099998699105559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279510698317466664932140745 209633023738099998699105559)
    ·
      refine ⟨314449535607149998048658339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209633023738099998699105559 314449535607149998048658339)
      ·
        refine ⟨471674303410724997072987509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314449535607149998048658339 471674303410724997072987509)
        ·
          refine ⟨44219465944755468475592579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 471674303410724997072987509 44219465944755468475592579)
          ·
            refine ⟨66329198917133202713388869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44219465944755468475592579 66329198917133202713388869)
            ·
              refine ⟨12436724796962475508760413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66329198917133202713388869 12436724796962475508760413)
              ·
                refine ⟨4663771798860928315785155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12436724796962475508760413 4663771798860928315785155)
                ·
                  refine ⟨6995657698291392473677733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4663771798860928315785155 6995657698291392473677733)
                  ·
                    refine ⟨1311685818429636088814575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6995657698291392473677733 1311685818429636088814575)
                    ·
                      rfl

theorem cell23_7663497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 1, 4].length) (baseStart_7663497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663497 prefixEnd_7663497 := by exact prefixLift 7663497
  have htrace : WordTrace (prefixWord ++ tailWord_7663497) baseStart_7663497 baseEnd_7663497 := by
    simpa [prefixWord, tailWord_7663497, baseEnd_7663497] using wordTrace_append hprefix tailTrace_7663497
  have hstable : (prefixWord ++ tailWord_7663497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663497).length < 2 ^ (prefixWord ++ tailWord_7663497).sum := by decide
  have hdescent : baseEnd_7663497 < baseStart_7663497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663527 : List Nat := [1, 1, 6, 1, 2, 2, 3, 1, 6]
def baseStart_7663527 : Nat := 118140960795 + 7663527 * 2 ^ 59
def prefixEnd_7663527 : Nat := 4983230072969 + 3 ^ 40 * 7663527 * 2
def baseEnd_7663527 : Nat := 437230317745393683229843

theorem tailTrace_7663527 : CollatzResearch.WordTrace tailWord_7663527 prefixEnd_7663527 437230317745393683229843 := by
  unfold tailWord_7663527
  simp only [CollatzResearch.WordTrace]
  refine ⟨279511792507357980055732835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186341195004905320037155223 279511792507357980055732835)
  ·
    refine ⟨419267688761036970083599253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279511792507357980055732835 419267688761036970083599253)
    ·
      refine ⟨19653172910673607972668715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 419267688761036970083599253 19653172910673607972668715)
      ·
        refine ⟨29479759366010411959003073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19653172910673607972668715 29479759366010411959003073)
        ·
          refine ⟨22109819524507808969252305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29479759366010411959003073 22109819524507808969252305)
          ·
            refine ⟨16582364643380856726939229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22109819524507808969252305 16582364643380856726939229)
            ·
              refine ⟨6218386741267821272602211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16582364643380856726939229 6218386741267821272602211)
              ·
                refine ⟨9327580111901731908903317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6218386741267821272602211 9327580111901731908903317)
                ·
                  refine ⟨437230317745393683229843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9327580111901731908903317 437230317745393683229843)
                  ·
                    rfl

theorem cell23_7663527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 6].length) (baseStart_7663527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663527 prefixEnd_7663527 := by exact prefixLift 7663527
  have htrace : WordTrace (prefixWord ++ tailWord_7663527) baseStart_7663527 baseEnd_7663527 := by
    simpa [prefixWord, tailWord_7663527, baseEnd_7663527] using wordTrace_append hprefix tailTrace_7663527
  have hstable : (prefixWord ++ tailWord_7663527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663527).length < 2 ^ (prefixWord ++ tailWord_7663527).sum := by decide
  have hdescent : baseEnd_7663527 < baseStart_7663527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663537 : List Nat := [1, 2, 2, 4, 2, 1, 2, 2, 3, 1, 3]
def baseStart_7663537 : Nat := 118140960795 + 7663537 * 2 ^ 59
def prefixEnd_7663537 : Nat := 4983230072969 + 3 ^ 40 * 7663537 * 2
def baseEnd_7663537 : Nat := 3935077994515088109943541

theorem tailTrace_7663537 : CollatzResearch.WordTrace tailWord_7663537 prefixEnd_7663537 3935077994515088109943541 := by
  unfold tailWord_7663537
  simp only [CollatzResearch.WordTrace]
  refine ⟨279512157237321751763596865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186341438158214501175731243 279512157237321751763596865)
  ·
    refine ⟨209634117927991313822697649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279512157237321751763596865 209634117927991313822697649)
    ·
      refine ⟨157225588445993485367023237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209634117927991313822697649 157225588445993485367023237)
      ·
        refine ⟨29479797833623778506316857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157225588445993485367023237 29479797833623778506316857)
        ·
          refine ⟨22109848375217833879737643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29479797833623778506316857 22109848375217833879737643)
          ·
            refine ⟨33164772562826750819606465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22109848375217833879737643 33164772562826750819606465)
            ·
              refine ⟨24873579422120063114704849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33164772562826750819606465 24873579422120063114704849)
              ·
                refine ⟨18655184566590047336028637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24873579422120063114704849 18655184566590047336028637)
                ·
                  refine ⟨6995694212471267751010739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18655184566590047336028637 6995694212471267751010739)
                  ·
                    refine ⟨10493541318706901626516109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6995694212471267751010739 10493541318706901626516109)
                    ·
                      refine ⟨3935077994515088109943541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10493541318706901626516109 3935077994515088109943541)
                      ·
                        rfl

theorem cell23_7663537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_7663537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663537 prefixEnd_7663537 := by exact prefixLift 7663537
  have htrace : WordTrace (prefixWord ++ tailWord_7663537) baseStart_7663537 baseEnd_7663537 := by
    simpa [prefixWord, tailWord_7663537, baseEnd_7663537] using wordTrace_append hprefix tailTrace_7663537
  have hstable : (prefixWord ++ tailWord_7663537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663537).length < 2 ^ (prefixWord ++ tailWord_7663537).sum := by decide
  have hdescent : baseEnd_7663537 < baseStart_7663537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663548 : List Nat := [2, 2, 2, 5, 2, 1, 1, 3, 1, 4]
def baseStart_7663548 : Nat := 118140960795 + 7663548 * 2 ^ 59
def prefixEnd_7663548 : Nat := 4983230072969 + 3 ^ 40 * 7663548 * 2
def baseEnd_7663548 : Nat := 1311694547600762522301997

theorem tailTrace_7663548 : CollatzResearch.WordTrace tailWord_7663548 prefixEnd_7663548 1311694547600762522301997 := by
  unfold tailWord_7663548
  simp only [CollatzResearch.WordTrace]
  refine ⟨139756279220140950321123649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186341705626854600428164865 139756279220140950321123649)
  ·
    refine ⟨104817209415105712740842737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139756279220140950321123649 104817209415105712740842737)
    ·
      refine ⟨78612907061329284555632053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104817209415105712740842737 78612907061329284555632053)
      ·
        refine ⟨7369960036999620427090505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78612907061329284555632053 7369960036999620427090505)
        ·
          refine ⟨5527470027749715320317879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7369960036999620427090505 5527470027749715320317879)
          ·
            refine ⟨8291205041624572980476819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5527470027749715320317879 8291205041624572980476819)
            ·
              refine ⟨12436807562436859470715229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8291205041624572980476819 12436807562436859470715229)
              ·
                refine ⟨4663802835913822301518211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12436807562436859470715229 4663802835913822301518211)
                ·
                  refine ⟨6995704253870733452277317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4663802835913822301518211 6995704253870733452277317)
                  ·
                    refine ⟨1311694547600762522301997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6995704253870733452277317 1311694547600762522301997)
                    ·
                      rfl

theorem cell23_7663548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_7663548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663548 prefixEnd_7663548 := by exact prefixLift 7663548
  have htrace : WordTrace (prefixWord ++ tailWord_7663548) baseStart_7663548 baseEnd_7663548 := by
    simpa [prefixWord, tailWord_7663548, baseEnd_7663548] using wordTrace_append hprefix tailTrace_7663548
  have hstable : (prefixWord ++ tailWord_7663548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663548).length < 2 ^ (prefixWord ++ tailWord_7663548).sum := by decide
  have hdescent : baseEnd_7663548 < baseStart_7663548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663583 : List Nat := [1, 1, 2, 3, 4, 1, 1, 10]
def baseStart_7663583 : Nat := 118140960795 + 7663583 * 2 ^ 59
def prefixEnd_7663583 : Nat := 4983230072969 + 3 ^ 40 * 7663583 * 2
def baseEnd_7663583 : Nat := 145744504245377589998827

theorem tailTrace_7663583 : CollatzResearch.WordTrace tailWord_7663583 prefixEnd_7663583 145744504245377589998827 := by
  unfold tailWord_7663583
  simp only [CollatzResearch.WordTrace]
  refine ⟨279513834995155101619771403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186342556663436734413180935 279513834995155101619771403)
  ·
    refine ⟨419270752492732652429657105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279513834995155101619771403 419270752492732652429657105)
    ·
      refine ⟨314453064369549489322242829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419270752492732652429657105 314453064369549489322242829)
      ·
        refine ⟨117919899138581058495841061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314453064369549489322242829 117919899138581058495841061)
        ·
          refine ⟨22109981088483948467970199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117919899138581058495841061 22109981088483948467970199)
          ·
            refine ⟨33164971632725922701955299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22109981088483948467970199 33164971632725922701955299)
            ·
              refine ⟨49747457449088884052932949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33164971632725922701955299 49747457449088884052932949)
              ·
                refine ⟨145744504245377589998827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49747457449088884052932949 145744504245377589998827)
                ·
                  rfl

theorem cell23_7663583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 10].length) (baseStart_7663583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663583 prefixEnd_7663583 := by exact prefixLift 7663583
  have htrace : WordTrace (prefixWord ++ tailWord_7663583) baseStart_7663583 baseEnd_7663583 := by
    simpa [prefixWord, tailWord_7663583, baseEnd_7663583] using wordTrace_append hprefix tailTrace_7663583
  have hstable : (prefixWord ++ tailWord_7663583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663583).length < 2 ^ (prefixWord ++ tailWord_7663583).sum := by decide
  have hdescent : baseEnd_7663583 < baseStart_7663583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663587 : List Nat := [1, 1, 1, 6, 1, 3, 1, 3, 2, 4]
def baseStart_7663587 : Nat := 118140960795 + 7663587 * 2 ^ 59
def prefixEnd_7663587 : Nat := 4983230072969 + 3 ^ 40 * 7663587 * 2
def baseEnd_7663587 : Nat := 1311701222849270971439437

theorem tailTrace_7663587 : CollatzResearch.WordTrace tailWord_7663587 prefixEnd_7663587 1311701222849270971439437 := by
  unfold tailWord_7663587
  simp only [CollatzResearch.WordTrace]
  refine ⟨279513980887140610302917015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186342653924760406868611343 279513980887140610302917015)
  ·
    refine ⟨419270971330710915454375523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279513980887140610302917015 419270971330710915454375523)
    ·
      refine ⟨628906456996066373181563285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419270971330710915454375523 628906456996066373181563285)
      ·
        refine ⟨29479990171690611242885779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 628906456996066373181563285 29479990171690611242885779)
        ·
          refine ⟨44219985257535916864328669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29479990171690611242885779 44219985257535916864328669)
          ·
            refine ⟨16582494471575968824123251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44219985257535916864328669 16582494471575968824123251)
            ·
              refine ⟨24873741707363953236184877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16582494471575968824123251 24873741707363953236184877)
              ·
                refine ⟨9327653140261482463569329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24873741707363953236184877 9327653140261482463569329)
                ·
                  refine ⟨6995739855196111847676997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9327653140261482463569329 6995739855196111847676997)
                  ·
                    refine ⟨1311701222849270971439437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6995739855196111847676997 1311701222849270971439437)
                    ·
                      rfl

theorem cell23_7663587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 4].length) (baseStart_7663587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663587 prefixEnd_7663587 := by exact prefixLift 7663587
  have htrace : WordTrace (prefixWord ++ tailWord_7663587) baseStart_7663587 baseEnd_7663587 := by
    simpa [prefixWord, tailWord_7663587, baseEnd_7663587] using wordTrace_append hprefix tailTrace_7663587
  have hstable : (prefixWord ++ tailWord_7663587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663587).length < 2 ^ (prefixWord ++ tailWord_7663587).sum := by decide
  have hdescent : baseEnd_7663587 < baseStart_7663587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663614 : List Nat := [4, 2, 2, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_7663614 : Nat := 118140960795 + 7663614 * 2 ^ 59
def prefixEnd_7663614 : Nat := 4983230072969 + 3 ^ 40 * 7663614 * 2
def baseEnd_7663614 : Nat := 3935117532525484308680687

theorem tailTrace_7663614 : CollatzResearch.WordTrace tailWord_7663614 prefixEnd_7663614 3935117532525484308680687 := by
  unfold tailWord_7663614
  simp only [CollatzResearch.WordTrace]
  refine ⟨34939370707255349239268737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186343310438695195942766597 34939370707255349239268737)
  ·
    refine ⟨26204528030441511929451553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34939370707255349239268737 26204528030441511929451553)
    ·
      refine ⟨19653396022831133947088665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26204528030441511929451553 19653396022831133947088665)
      ·
        refine ⟨14740047017123350460316499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19653396022831133947088665 14740047017123350460316499)
        ·
          refine ⟨22110070525685025690474749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14740047017123350460316499 22110070525685025690474749)
          ·
            refine ⟨8291276447131884633928031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22110070525685025690474749 8291276447131884633928031)
            ·
              refine ⟨12436914670697826950892047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8291276447131884633928031 12436914670697826950892047)
              ·
                refine ⟨18655372006046740426338071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12436914670697826950892047 18655372006046740426338071)
                ·
                  refine ⟨27983058009070110639507107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18655372006046740426338071 27983058009070110639507107)
                  ·
                    refine ⟨41974587013605165959260661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27983058009070110639507107 41974587013605165959260661)
                    ·
                      refine ⟨3935117532525484308680687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41974587013605165959260661 3935117532525484308680687)
                      ·
                        rfl

theorem cell23_7663614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_7663614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663614 prefixEnd_7663614 := by exact prefixLift 7663614
  have htrace : WordTrace (prefixWord ++ tailWord_7663614) baseStart_7663614 baseEnd_7663614 := by
    simpa [prefixWord, tailWord_7663614, baseEnd_7663614] using wordTrace_append hprefix tailTrace_7663614
  have hstable : (prefixWord ++ tailWord_7663614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663614).length < 2 ^ (prefixWord ++ tailWord_7663614).sum := by decide
  have hdescent : baseEnd_7663614 < baseStart_7663614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663622 : List Nat := [6, 2, 1, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_7663622 : Nat := 118140960795 + 7663622 * 2 ^ 59
def prefixEnd_7663622 : Nat := 4983230072969 + 3 ^ 40 * 7663622 * 2
def baseEnd_7663622 : Nat := 3935121640370720277380651

theorem tailTrace_7663622 : CollatzResearch.WordTrace tailWord_7663622 prefixEnd_7663622 3935121640370720277380651 := by
  unfold tailWord_7663622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8734851795062931602513785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 186343504961342540853627413 8734851795062931602513785)
  ·
    refine ⟨6551138846297198701885339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8734851795062931602513785 6551138846297198701885339)
    ·
      refine ⟨9826708269445798052828009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6551138846297198701885339 9826708269445798052828009)
      ·
        refine ⟨7370031202084348539621007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9826708269445798052828009 7370031202084348539621007)
        ·
          refine ⟨11055046803126522809431511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7370031202084348539621007 11055046803126522809431511)
          ·
            refine ⟨16582570204689784214147267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11055046803126522809431511 16582570204689784214147267)
            ·
              refine ⟨24873855307034676321220901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16582570204689784214147267 24873855307034676321220901)
              ·
                refine ⟨4663847870069001810228919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24873855307034676321220901 4663847870069001810228919)
                ·
                  refine ⟨6995771805103502715343379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4663847870069001810228919 6995771805103502715343379)
                  ·
                    refine ⟨10493657707655254073015069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6995771805103502715343379 10493657707655254073015069)
                    ·
                      refine ⟨3935121640370720277380651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10493657707655254073015069 3935121640370720277380651)
                      ·
                        rfl

theorem cell23_7663622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_7663622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663622 prefixEnd_7663622 := by exact prefixLift 7663622
  have htrace : WordTrace (prefixWord ++ tailWord_7663622) baseStart_7663622 baseEnd_7663622 := by
    simpa [prefixWord, tailWord_7663622, baseEnd_7663622] using wordTrace_append hprefix tailTrace_7663622
  have hstable : (prefixWord ++ tailWord_7663622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663622).length < 2 ^ (prefixWord ++ tailWord_7663622).sum := by decide
  have hdescent : baseEnd_7663622 < baseStart_7663622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663644 : List Nat := [2, 2, 3, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_7663644 : Nat := 118140960795 + 7663644 * 2 ^ 59
def prefixEnd_7663644 : Nat := 4983230072969 + 3 ^ 40 * 7663644 * 2
def baseEnd_7663644 : Nat := 3935132936945119191305549

theorem tailTrace_7663644 : CollatzResearch.WordTrace tailWord_7663644 prefixEnd_7663644 3935132936945119191305549 := by
  unfold tailWord_7663644
  simp only [CollatzResearch.WordTrace]
  refine ⟨139758029923967054518870993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186344039898622739358494657 139758029923967054518870993)
  ·
    refine ⟨104818522442975290889153245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139758029923967054518870993 104818522442975290889153245)
    ·
      refine ⟨39306945916115734083432467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104818522442975290889153245 39306945916115734083432467)
      ·
        refine ⟨58960418874173601125148701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39306945916115734083432467 58960418874173601125148701)
        ·
          refine ⟨22110157077815100421930763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58960418874173601125148701 22110157077815100421930763)
          ·
            refine ⟨33165235616722650632896145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22110157077815100421930763 33165235616722650632896145)
            ·
              refine ⟨24873926712541987974672109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33165235616722650632896145 24873926712541987974672109)
              ·
                refine ⟨9327722517203245490502041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24873926712541987974672109 9327722517203245490502041)
                ·
                  refine ⟨6995791887902434117876531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9327722517203245490502041 6995791887902434117876531)
                  ·
                    refine ⟨10493687831853651176814797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6995791887902434117876531 10493687831853651176814797)
                    ·
                      refine ⟨3935132936945119191305549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10493687831853651176814797 3935132936945119191305549)
                      ·
                        rfl

theorem cell23_7663644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_7663644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663644 prefixEnd_7663644 := by exact prefixLift 7663644
  have htrace : WordTrace (prefixWord ++ tailWord_7663644) baseStart_7663644 baseEnd_7663644 := by
    simpa [prefixWord, tailWord_7663644, baseEnd_7663644] using wordTrace_append hprefix tailTrace_7663644
  have hstable : (prefixWord ++ tailWord_7663644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663644).length < 2 ^ (prefixWord ++ tailWord_7663644).sum := by decide
  have hdescent : baseEnd_7663644 < baseStart_7663644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663650 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_7663650 : Nat := 118140960795 + 7663650 * 2 ^ 59
def prefixEnd_7663650 : Nat := 4983230072969 + 3 ^ 40 * 7663650 * 2
def baseEnd_7663650 : Nat := 3935136017829046167830521

theorem tailTrace_7663650 : CollatzResearch.WordTrace tailWord_7663650 prefixEnd_7663650 3935136017829046167830521 := by
  unfold tailWord_7663650
  simp only [CollatzResearch.WordTrace]
  refine ⟨69879069671478093015615101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186344185790608248041640269 69879069671478093015615101)
  ·
    refine ⟨26204651126804284880855663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69879069671478093015615101 26204651126804284880855663)
    ·
      refine ⟨39306976690206427321283495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26204651126804284880855663 39306976690206427321283495)
      ·
        refine ⟨58960465035309640981925243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39306976690206427321283495 58960465035309640981925243)
        ·
          refine ⟨88440697552964461472887865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58960465035309640981925243 88440697552964461472887865)
          ·
            refine ⟨66330523164723346104665899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88440697552964461472887865 66330523164723346104665899)
            ·
              refine ⟨99495784747085019156998849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66330523164723346104665899 99495784747085019156998849)
              ·
                refine ⟨74621838560313764367749137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99495784747085019156998849 74621838560313764367749137)
                ·
                  refine ⟨55966378920235323275811853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74621838560313764367749137 55966378920235323275811853)
                  ·
                    refine ⟨20987392095088246228429445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55966378920235323275811853 20987392095088246228429445)
                    ·
                      refine ⟨3935136017829046167830521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20987392095088246228429445 3935136017829046167830521)
                      ·
                        rfl

theorem cell23_7663650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_7663650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663650 prefixEnd_7663650 := by exact prefixLift 7663650
  have htrace : WordTrace (prefixWord ++ tailWord_7663650) baseStart_7663650 baseEnd_7663650 := by
    simpa [prefixWord, tailWord_7663650, baseEnd_7663650] using wordTrace_append hprefix tailTrace_7663650
  have hstable : (prefixWord ++ tailWord_7663650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663650).length < 2 ^ (prefixWord ++ tailWord_7663650).sum := by decide
  have hdescent : baseEnd_7663650 < baseStart_7663650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663667 : List Nat := [1, 1, 1, 2, 4, 1, 4, 2, 1, 4, 2]
def baseStart_7663667 : Nat := 118140960795 + 7663667 * 2 ^ 59
def prefixEnd_7663667 : Nat := 4983230072969 + 3 ^ 40 * 7663667 * 2
def baseEnd_7663667 : Nat := 3935144747000172601317943

theorem tailTrace_7663667 : CollatzResearch.WordTrace tailWord_7663667 prefixEnd_7663667 3935144747000172601317943 := by
  unfold tailWord_7663667
  simp only [CollatzResearch.WordTrace]
  refine ⟨279516898726850783965829255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186344599151233855977219503 279516898726850783965829255)
  ·
    refine ⟨419275348090276175948743883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279516898726850783965829255 419275348090276175948743883)
    ·
      refine ⟨628913022135414263923115825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419275348090276175948743883 628913022135414263923115825)
      ·
        refine ⟨471684766601560697942336869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628913022135414263923115825 471684766601560697942336869)
        ·
          refine ⟨88440893737792630864188163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 471684766601560697942336869 88440893737792630864188163)
          ·
            refine ⟨132661340606688946296282245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88440893737792630864188163 132661340606688946296282245)
            ·
              refine ⟨24874001363754177430552921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132661340606688946296282245 24874001363754177430552921)
              ·
                refine ⟨18655501022815633072914691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24874001363754177430552921 18655501022815633072914691)
                ·
                  refine ⟨27983251534223449609372037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18655501022815633072914691 27983251534223449609372037)
                  ·
                    refine ⟨5246859662666896801757257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27983251534223449609372037 5246859662666896801757257)
                    ·
                      refine ⟨3935144747000172601317943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5246859662666896801757257 3935144747000172601317943)
                      ·
                        rfl

theorem cell23_7663667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 4, 2].length) (baseStart_7663667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663667 prefixEnd_7663667 := by exact prefixLift 7663667
  have htrace : WordTrace (prefixWord ++ tailWord_7663667) baseStart_7663667 baseEnd_7663667 := by
    simpa [prefixWord, tailWord_7663667, baseEnd_7663667] using wordTrace_append hprefix tailTrace_7663667
  have hstable : (prefixWord ++ tailWord_7663667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663667).length < 2 ^ (prefixWord ++ tailWord_7663667).sum := by decide
  have hdescent : baseEnd_7663667 < baseStart_7663667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663678 : List Nat := [4, 2, 1, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_7663678 : Nat := 118140960795 + 7663678 * 2 ^ 59
def prefixEnd_7663678 : Nat := 4983230072969 + 3 ^ 40 * 7663678 * 2
def baseEnd_7663678 : Nat := 3935150395287372058280393

theorem tailTrace_7663678 : CollatzResearch.WordTrace tailWord_7663678 prefixEnd_7663678 3935150395287372058280393 := by
  unfold tailWord_7663678
  simp only [CollatzResearch.WordTrace]
  refine ⟨34939662491226366605559961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186344866619873955229653125 34939662491226366605559961)
  ·
    refine ⟨26204746868419774954169971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34939662491226366605559961 26204746868419774954169971)
    ·
      refine ⟨39307120302629662431254957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26204746868419774954169971 39307120302629662431254957)
      ·
        refine ⟨14740170113486123411720609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39307120302629662431254957 14740170113486123411720609)
        ·
          refine ⟨11055127585114592558790457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14740170113486123411720609 11055127585114592558790457)
          ·
            refine ⟨8291345688835944419092843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11055127585114592558790457 8291345688835944419092843)
            ·
              refine ⟨12437018533253916628639265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8291345688835944419092843 12437018533253916628639265)
              ·
                refine ⟨9327763899940437471479449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12437018533253916628639265 9327763899940437471479449)
                ·
                  refine ⟨6995822924955328103609587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9327763899940437471479449 6995822924955328103609587)
                  ·
                    refine ⟨10493734387432992155414381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6995822924955328103609587 10493734387432992155414381)
                    ·
                      refine ⟨3935150395287372058280393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10493734387432992155414381 3935150395287372058280393)
                      ·
                        rfl

theorem cell23_7663678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_7663678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663678 prefixEnd_7663678 := by exact prefixLift 7663678
  have htrace : WordTrace (prefixWord ++ tailWord_7663678) baseStart_7663678 baseEnd_7663678 := by
    simpa [prefixWord, tailWord_7663678, baseEnd_7663678] using wordTrace_append hprefix tailTrace_7663678
  have hstable : (prefixWord ++ tailWord_7663678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663678).length < 2 ^ (prefixWord ++ tailWord_7663678).sum := by decide
  have hdescent : baseEnd_7663678 < baseStart_7663678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663680 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 4]
def baseStart_7663680 : Nat := 118140960795 + 7663680 * 2 ^ 59
def prefixEnd_7663680 : Nat := 4983230072969 + 3 ^ 40 * 7663680 * 2
def baseEnd_7663680 : Nat := 3935151422248681050455383

theorem tailTrace_7663680 : CollatzResearch.WordTrace tailWord_7663680 prefixEnd_7663680 3935151422248681050455383 := by
  unfold tailWord_7663680
  simp only [CollatzResearch.WordTrace]
  refine ⟨139758686437901843593026247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186344915250535791457368329 139758686437901843593026247)
  ·
    refine ⟨209638029656852765389539371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139758686437901843593026247 209638029656852765389539371)
    ·
      refine ⟨314457044485279148084309057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209638029656852765389539371 314457044485279148084309057)
      ·
        refine ⟨235842783363959361063231793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314457044485279148084309057 235842783363959361063231793)
        ·
          refine ⟨176882087522969520797423845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235842783363959361063231793 176882087522969520797423845)
          ·
            refine ⟨33165391410556785149516971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176882087522969520797423845 33165391410556785149516971)
            ·
              refine ⟨49748087115835177724275457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33165391410556785149516971 49748087115835177724275457)
              ·
                refine ⟨37311065336876383293206593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49748087115835177724275457 37311065336876383293206593)
                ·
                  refine ⟨27983299002657287469904945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37311065336876383293206593 27983299002657287469904945)
                  ·
                    refine ⟨20987474251992965602428709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27983299002657287469904945 20987474251992965602428709)
                    ·
                      refine ⟨3935151422248681050455383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20987474251992965602428709 3935151422248681050455383)
                      ·
                        rfl

theorem cell23_7663680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_7663680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663680 prefixEnd_7663680 := by exact prefixLift 7663680
  have htrace : WordTrace (prefixWord ++ tailWord_7663680) baseStart_7663680 baseEnd_7663680 := by
    simpa [prefixWord, tailWord_7663680, baseEnd_7663680] using wordTrace_append hprefix tailTrace_7663680
  have hstable : (prefixWord ++ tailWord_7663680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663680).length < 2 ^ (prefixWord ++ tailWord_7663680).sum := by decide
  have hdescent : baseEnd_7663680 < baseStart_7663680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663683 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 9]
def baseStart_7663683 : Nat := 118140960795 + 7663683 * 2 ^ 59
def prefixEnd_7663683 : Nat := 4983230072969 + 3 ^ 40 * 7663683 * 2
def baseEnd_7663683 : Nat := 3935152962690644538717869

theorem tailTrace_7663683 : CollatzResearch.WordTrace tailWord_7663683 prefixEnd_7663683 3935152962690644538717869 := by
  unfold tailWord_7663683
  simp only [CollatzResearch.WordTrace]
  refine ⟨279517482294792818698411703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186344988196528545798941135 279517482294792818698411703)
  ·
    refine ⟨419276223442189228047617555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279517482294792818698411703 419276223442189228047617555)
    ·
      refine ⟨628914335163283842071426333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419276223442189228047617555 628914335163283842071426333)
      ·
        refine ⟨235842875686231440776784875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 628914335163283842071426333 235842875686231440776784875)
        ·
          refine ⟨353764313529347161165177313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235842875686231440776784875 353764313529347161165177313)
          ·
            refine ⟨265323235147010370873882985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353764313529347161165177313 265323235147010370873882985)
            ·
              refine ⟨198992426360257778155412239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265323235147010370873882985 198992426360257778155412239)
              ·
                refine ⟨298488639540386667233118359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198992426360257778155412239 298488639540386667233118359)
                ·
                  refine ⟨447732959310580000849677539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298488639540386667233118359 447732959310580000849677539)
                  ·
                    refine ⟨671599438965870001274516309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 447732959310580000849677539 671599438965870001274516309)
                    ·
                      refine ⟨3935152962690644538717869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 671599438965870001274516309 3935152962690644538717869)
                      ·
                        rfl

theorem cell23_7663683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_7663683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663683 prefixEnd_7663683 := by exact prefixLift 7663683
  have htrace : WordTrace (prefixWord ++ tailWord_7663683) baseStart_7663683 baseEnd_7663683 := by
    simpa [prefixWord, tailWord_7663683, baseEnd_7663683] using wordTrace_append hprefix tailTrace_7663683
  have hstable : (prefixWord ++ tailWord_7663683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663683).length < 2 ^ (prefixWord ++ tailWord_7663683).sum := by decide
  have hdescent : baseEnd_7663683 < baseStart_7663683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663724 : List Nat := [2, 2, 1, 1, 3, 5, 1, 3, 5]
def baseStart_7663724 : Nat := 118140960795 + 7663724 * 2 ^ 59
def prefixEnd_7663724 : Nat := 4983230072969 + 3 ^ 40 * 7663724 * 2
def baseEnd_7663724 : Nat := 437241557266386542033909

theorem tailTrace_7663724 : CollatzResearch.WordTrace tailWord_7663724 prefixEnd_7663724 437241557266386542033909 := by
  unfold tailWord_7663724
  simp only [CollatzResearch.WordTrace]
  refine ⟨139759488843822141350327113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186345985125096188467102817 139759488843822141350327113)
  ·
    refine ⟨104819616632866606012745335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139759488843822141350327113 104819616632866606012745335)
    ·
      refine ⟨157229424949299909019118003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104819616632866606012745335 157229424949299909019118003)
      ·
        refine ⟨235844137423949863528677005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157229424949299909019118003 235844137423949863528677005)
        ·
          refine ⟨88441551533981198823253877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235844137423949863528677005 88441551533981198823253877)
          ·
            refine ⟨8291395456310737389680051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88441551533981198823253877 8291395456310737389680051)
            ·
              refine ⟨12437093184466106084520077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8291395456310737389680051 12437093184466106084520077)
              ·
                refine ⟨4663909944174789781695029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12437093184466106084520077 4663909944174789781695029)
                ·
                  refine ⟨437241557266386542033909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4663909944174789781695029 437241557266386542033909)
                  ·
                    rfl

theorem cell23_7663724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 5].length) (baseStart_7663724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663724 prefixEnd_7663724 := by exact prefixLift 7663724
  have htrace : WordTrace (prefixWord ++ tailWord_7663724) baseStart_7663724 baseEnd_7663724 := by
    simpa [prefixWord, tailWord_7663724, baseEnd_7663724] using wordTrace_append hprefix tailTrace_7663724
  have hstable : (prefixWord ++ tailWord_7663724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663724).length < 2 ^ (prefixWord ++ tailWord_7663724).sum := by decide
  have hdescent : baseEnd_7663724 < baseStart_7663724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663737 : List Nat := [1, 2, 1, 3, 4, 2, 1, 2, 2, 5]
def baseStart_7663737 : Nat := 118140960795 + 7663737 * 2 ^ 59
def prefixEnd_7663737 : Nat := 4983230072969 + 3 ^ 40 * 7663737 * 2
def baseEnd_7663737 : Nat := 1311726896881995775814207

theorem tailTrace_7663737 : CollatzResearch.WordTrace tailWord_7663737 prefixEnd_7663737 1311726896881995775814207 := by
  unfold tailWord_7663737
  simp only [CollatzResearch.WordTrace]
  refine ⟨279519451836597185920877465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186346301224398123947251643 279519451836597185920877465)
  ·
    refine ⟨209639588877447889440658099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279519451836597185920877465 209639588877447889440658099)
    ·
      refine ⟨314459383316171834160987149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209639588877447889440658099 314459383316171834160987149)
      ·
        refine ⟨117922268743564437810370181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314459383316171834160987149 117922268743564437810370181)
        ·
          refine ⟨22110425389418332089444409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117922268743564437810370181 22110425389418332089444409)
          ·
            refine ⟨16582819042063749067083307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22110425389418332089444409 16582819042063749067083307)
            ·
              refine ⟨24874228563095623600624961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16582819042063749067083307 24874228563095623600624961)
              ·
                refine ⟨18655671422321717700468721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24874228563095623600624961 18655671422321717700468721)
                ·
                  refine ⟨13991753566741288275351541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18655671422321717700468721 13991753566741288275351541)
                  ·
                    refine ⟨1311726896881995775814207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13991753566741288275351541 1311726896881995775814207)
                    ·
                      rfl

theorem cell23_7663737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 5].length) (baseStart_7663737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663737 prefixEnd_7663737 := by exact prefixLift 7663737
  have htrace : WordTrace (prefixWord ++ tailWord_7663737) baseStart_7663737 baseEnd_7663737 := by
    simpa [prefixWord, tailWord_7663737, baseEnd_7663737] using wordTrace_append hprefix tailTrace_7663737
  have hstable : (prefixWord ++ tailWord_7663737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663737).length < 2 ^ (prefixWord ++ tailWord_7663737).sum := by decide
  have hdescent : baseEnd_7663737 < baseStart_7663737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663800 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 1, 2, 6]
def baseStart_7663800 : Nat := 118140960795 + 7663800 * 2 ^ 59
def prefixEnd_7663800 : Nat := 4983230072969 + 3 ^ 40 * 7663800 * 2
def baseEnd_7663800 : Nat := 3935213039927220580954831

theorem tailTrace_7663800 : CollatzResearch.WordTrace tailWord_7663800 prefixEnd_7663800 3935213039927220580954831 := by
  unfold tailWord_7663800
  simp only [CollatzResearch.WordTrace]
  refine ⟨139760874817684473840210427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186347833090245965120280569 139760874817684473840210427)
  ·
    refine ⟨209641312226526710760315641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139760874817684473840210427 209641312226526710760315641)
    ·
      refine ⟨157230984169895033070236731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209641312226526710760315641 157230984169895033070236731)
      ·
        refine ⟨235846476254842549605355097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157230984169895033070236731 235846476254842549605355097)
        ·
          refine ⟨176884857191131912204016323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235846476254842549605355097 176884857191131912204016323)
          ·
            refine ⟨265327285786697868306024485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176884857191131912204016323 265327285786697868306024485)
            ·
              refine ⟨49748866085005850307379591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265327285786697868306024485 49748866085005850307379591)
              ·
                refine ⟨74623299127508775461069387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49748866085005850307379591 74623299127508775461069387)
                ·
                  refine ⟨111934948691263163191604081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74623299127508775461069387 111934948691263163191604081)
                  ·
                    refine ⟨83951211518447372393703061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111934948691263163191604081 83951211518447372393703061)
                    ·
                      refine ⟨3935213039927220580954831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83951211518447372393703061 3935213039927220580954831)
                      ·
                        rfl

theorem cell23_7663800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_7663800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663800 prefixEnd_7663800 := by exact prefixLift 7663800
  have htrace : WordTrace (prefixWord ++ tailWord_7663800) baseStart_7663800 baseEnd_7663800 := by
    simpa [prefixWord, tailWord_7663800, baseEnd_7663800] using wordTrace_append hprefix tailTrace_7663800
  have hstable : (prefixWord ++ tailWord_7663800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663800).length < 2 ^ (prefixWord ++ tailWord_7663800).sum := by decide
  have hdescent : baseEnd_7663800 < baseStart_7663800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663858 : List Nat := [3, 2, 1, 3, 2, 1, 2, 4, 1, 1, 3]
def baseStart_7663858 : Nat := 118140960795 + 7663858 * 2 ^ 59
def prefixEnd_7663858 : Nat := 4983230072969 + 3 ^ 40 * 7663858 * 2
def baseEnd_7663858 : Nat := 3935242821805181354029565

theorem tailTrace_7663858 : CollatzResearch.WordTrace tailWord_7663858 prefixEnd_7663858 3935242821805181354029565 := by
  unfold tailWord_7663858
  simp only [CollatzResearch.WordTrace]
  refine ⟨69880966267289705896508057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186349243379439215724021485 69880966267289705896508057)
  ·
    refine ⟨52410724700467279422381043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69880966267289705896508057 52410724700467279422381043)
    ·
      refine ⟨78616087050700919133571565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52410724700467279422381043 78616087050700919133571565)
      ·
        refine ⟨29481032644012844675089337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78616087050700919133571565 29481032644012844675089337)
        ·
          refine ⟨22110774483009633506317003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29481032644012844675089337 22110774483009633506317003)
          ·
            refine ⟨33166161724514450259475505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22110774483009633506317003 33166161724514450259475505)
            ·
              refine ⟨24874621293385837694606629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33166161724514450259475505 24874621293385837694606629)
              ·
                refine ⟨4663991492509844567738743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24874621293385837694606629 4663991492509844567738743)
                ·
                  refine ⟨6995987238764766851608115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4663991492509844567738743 6995987238764766851608115)
                  ·
                    refine ⟨10493980858147150277412173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6995987238764766851608115 10493980858147150277412173)
                    ·
                      refine ⟨3935242821805181354029565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10493980858147150277412173 3935242821805181354029565)
                      ·
                        rfl

theorem cell23_7663858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_7663858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663858 prefixEnd_7663858 := by exact prefixLift 7663858
  have htrace : WordTrace (prefixWord ++ tailWord_7663858) baseStart_7663858 baseEnd_7663858 := by
    simpa [prefixWord, tailWord_7663858, baseEnd_7663858] using wordTrace_append hprefix tailTrace_7663858
  have hstable : (prefixWord ++ tailWord_7663858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663858).length < 2 ^ (prefixWord ++ tailWord_7663858).sum := by decide
  have hdescent : baseEnd_7663858 < baseStart_7663858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663877 : List Nat := [1, 3, 1, 1, 2, 1, 2, 5, 1, 2, 4]
def baseStart_7663877 : Nat := 118140960795 + 7663877 * 2 ^ 59
def prefixEnd_7663877 : Nat := 4983230072969 + 3 ^ 40 * 7663877 * 2
def baseEnd_7663877 : Nat := 3935252577937616779691977

theorem tailTrace_7663877 : CollatzResearch.WordTrace tailWord_7663877 prefixEnd_7663877 3935252577937616779691977 := by
  unfold tailWord_7663877
  simp only [CollatzResearch.WordTrace]
  refine ⟨279524558056089989830973885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186349705370726659887315923 279524558056089989830973885)
  ·
    refine ⟨104821709271033746186615207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279524558056089989830973885 104821709271033746186615207)
    ·
      refine ⟨157232563906550619279922811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104821709271033746186615207 157232563906550619279922811)
      ·
        refine ⟨235848845859825928919884217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157232563906550619279922811 235848845859825928919884217)
        ·
          refine ⟨176886634394869446689913163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235848845859825928919884217 176886634394869446689913163)
          ·
            refine ⟨265329951592304170034869745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176886634394869446689913163 265329951592304170034869745)
            ·
              refine ⟨198997463694228127526152309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265329951592304170034869745 198997463694228127526152309)
              ·
                refine ⟨18656012221333886955576779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198997463694228127526152309 18656012221333886955576779)
                ·
                  refine ⟨27984018332000830433365169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18656012221333886955576779 27984018332000830433365169)
                  ·
                    refine ⟨20988013749000622825023877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27984018332000830433365169 20988013749000622825023877)
                    ·
                      refine ⟨3935252577937616779691977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20988013749000622825023877 3935252577937616779691977)
                      ·
                        rfl

theorem cell23_7663877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_7663877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663877 prefixEnd_7663877 := by exact prefixLift 7663877
  have htrace : WordTrace (prefixWord ++ tailWord_7663877) baseStart_7663877 baseEnd_7663877 := by
    simpa [prefixWord, tailWord_7663877, baseEnd_7663877] using wordTrace_append hprefix tailTrace_7663877
  have hstable : (prefixWord ++ tailWord_7663877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663877).length < 2 ^ (prefixWord ++ tailWord_7663877).sum := by decide
  have hdescent : baseEnd_7663877 < baseStart_7663877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663881 : List Nat := [1, 2, 1, 1, 3, 4, 2, 2, 3, 2, 2]
def baseStart_7663881 : Nat := 118140960795 + 7663881 * 2 ^ 59
def prefixEnd_7663881 : Nat := 4983230072969 + 3 ^ 40 * 7663881 * 2
def baseEnd_7663881 : Nat := 3935254631860234764041959

theorem tailTrace_7663881 : CollatzResearch.WordTrace tailWord_7663881 prefixEnd_7663881 3935254631860234764041959 := by
  unfold tailWord_7663881
  simp only [CollatzResearch.WordTrace]
  refine ⟨279524703948075498514119497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186349802632050332342746331 279524703948075498514119497)
  ·
    refine ⟨209643527961056623885589623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279524703948075498514119497 209643527961056623885589623)
    ·
      refine ⟨314465291941584935828384435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209643527961056623885589623 314465291941584935828384435)
      ·
        refine ⟨471697937912377403742576653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314465291941584935828384435 471697937912377403742576653)
        ·
          refine ⟨176886726717141526403466245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 471697937912377403742576653 176886726717141526403466245)
          ·
            refine ⟨33166261259464036200649921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176886726717141526403466245 33166261259464036200649921)
            ·
              refine ⟨24874695944598027150487441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33166261259464036200649921 24874695944598027150487441)
              ·
                refine ⟨18656021958448520362865581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24874695944598027150487441 18656021958448520362865581)
                ·
                  refine ⟨6996008234418195136074593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18656021958448520362865581 6996008234418195136074593)
                  ·
                    refine ⟨5247006175813646352055945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6996008234418195136074593 5247006175813646352055945)
                    ·
                      refine ⟨3935254631860234764041959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5247006175813646352055945 3935254631860234764041959)
                      ·
                        rfl

theorem cell23_7663881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 2, 2].length) (baseStart_7663881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663881 prefixEnd_7663881 := by exact prefixLift 7663881
  have htrace : WordTrace (prefixWord ++ tailWord_7663881) baseStart_7663881 baseEnd_7663881 := by
    simpa [prefixWord, tailWord_7663881, baseEnd_7663881] using wordTrace_append hprefix tailTrace_7663881
  have hstable : (prefixWord ++ tailWord_7663881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663881).length < 2 ^ (prefixWord ++ tailWord_7663881).sum := by decide
  have hdescent : baseEnd_7663881 < baseStart_7663881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663901 : List Nat := [1, 4, 2, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_7663901 : Nat := 118140960795 + 7663901 * 2 ^ 59
def prefixEnd_7663901 : Nat := 4983230072969 + 3 ^ 40 * 7663901 * 2
def baseEnd_7663901 : Nat := 3935264901473324685791867

theorem tailTrace_7663901 : CollatzResearch.WordTrace tailWord_7663901 prefixEnd_7663901 3935264901473324685791867 := by
  unfold tailWord_7663901
  simp only [CollatzResearch.WordTrace]
  refine ⟨279525433408003041929847557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186350288938668694619898371 279525433408003041929847557)
  ·
    refine ⟨52411018764000570361846417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279525433408003041929847557 52411018764000570361846417)
    ·
      refine ⟨39308264073000427771384813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52411018764000570361846417 39308264073000427771384813)
      ·
        refine ⟨14740599027375160414269305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39308264073000427771384813 14740599027375160414269305)
        ·
          refine ⟨11055449270531370310701979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14740599027375160414269305 11055449270531370310701979)
          ·
            refine ⟨16583173905797055466052969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11055449270531370310701979 16583173905797055466052969)
            ·
              refine ⟨12437380429347791599539727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16583173905797055466052969 12437380429347791599539727)
              ·
                refine ⟨18656070644021687399309591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12437380429347791599539727 18656070644021687399309591)
                ·
                  refine ⟨27984105966032531098964387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18656070644021687399309591 27984105966032531098964387)
                  ·
                    refine ⟨41976158949048796648446581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27984105966032531098964387 41976158949048796648446581)
                    ·
                      refine ⟨3935264901473324685791867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41976158949048796648446581 3935264901473324685791867)
                      ·
                        rfl

theorem cell23_7663901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_7663901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663901 prefixEnd_7663901 := by exact prefixLift 7663901
  have htrace : WordTrace (prefixWord ++ tailWord_7663901) baseStart_7663901 baseEnd_7663901 := by
    simpa [prefixWord, tailWord_7663901, baseEnd_7663901] using wordTrace_append hprefix tailTrace_7663901
  have hstable : (prefixWord ++ tailWord_7663901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663901).length < 2 ^ (prefixWord ++ tailWord_7663901).sum := by decide
  have hdescent : baseEnd_7663901 < baseStart_7663901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663977 : List Nat := [1, 2, 1, 1, 1, 3, 4, 3, 7]
def baseStart_7663977 : Nat := 118140960795 + 7663977 * 2 ^ 59
def prefixEnd_7663977 : Nat := 4983230072969 + 3 ^ 40 * 7663977 * 2
def baseEnd_7663977 : Nat := 437255991778118487604613

theorem tailTrace_7663977 : CollatzResearch.WordTrace tailWord_7663977 prefixEnd_7663977 437255991778118487604613 := by
  unfold tailWord_7663977
  simp only [CollatzResearch.WordTrace]
  refine ⟨279528205355727706909614185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186352136903818471273076123 279528205355727706909614185)
  ·
    refine ⟨209646154016795780182210639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279528205355727706909614185 209646154016795780182210639)
    ·
      refine ⟨314469231025193670273315959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209646154016795780182210639 314469231025193670273315959)
      ·
        refine ⟨471703846537790505409973939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314469231025193670273315959 471703846537790505409973939)
        ·
          refine ⟨707555769806685758114960909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471703846537790505409973939 707555769806685758114960909)
          ·
            refine ⟨265333413677507159293110341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 707555769806685758114960909 265333413677507159293110341)
            ·
              refine ⟨49750015064532592367458189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265333413677507159293110341 49750015064532592367458189)
              ·
                refine ⟨18656255649199722137796821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49750015064532592367458189 18656255649199722137796821)
                ·
                  refine ⟨437255991778118487604613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18656255649199722137796821 437255991778118487604613)
                  ·
                    rfl

theorem cell23_7663977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 7].length) (baseStart_7663977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663977 prefixEnd_7663977 := by exact prefixLift 7663977
  have htrace : WordTrace (prefixWord ++ tailWord_7663977) baseStart_7663977 baseEnd_7663977 := by
    simpa [prefixWord, tailWord_7663977, baseEnd_7663977] using wordTrace_append hprefix tailTrace_7663977
  have hstable : (prefixWord ++ tailWord_7663977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663977).length < 2 ^ (prefixWord ++ tailWord_7663977).sum := by decide
  have hdescent : baseEnd_7663977 < baseStart_7663977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7663984 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 4]
def baseStart_7663984 : Nat := 118140960795 + 7663984 * 2 ^ 59
def prefixEnd_7663984 : Nat := 4983230072969 + 3 ^ 40 * 7663984 * 2
def baseEnd_7663984 : Nat := 3935307520367647861053985

theorem tailTrace_7663984 : CollatzResearch.WordTrace tailWord_7663984 prefixEnd_7663984 3935307520367647861053985 := by
  unfold tailWord_7663984
  simp only [CollatzResearch.WordTrace]
  refine ⟨139764230333351173552559503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186352307111134898070079337 139764230333351173552559503)
  ·
    refine ⟨209646345500026760328839255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139764230333351173552559503 209646345500026760328839255)
    ·
      refine ⟨314469518250040140493258883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209646345500026760328839255 314469518250040140493258883)
      ·
        refine ⟨471704277375060210739888325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314469518250040140493258883 471704277375060210739888325)
        ·
          refine ⟨88444552007823789513729061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 471704277375060210739888325 88444552007823789513729061)
          ·
            refine ⟨16583353501466960533824199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88444552007823789513729061 16583353501466960533824199)
            ·
              refine ⟨24875030252200440800736299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16583353501466960533824199 24875030252200440800736299)
              ·
                refine ⟨37312545378300661201104449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24875030252200440800736299 37312545378300661201104449)
                ·
                  refine ⟨27984409033725495900828337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37312545378300661201104449 27984409033725495900828337)
                  ·
                    refine ⟨20988306775294121925621253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27984409033725495900828337 20988306775294121925621253)
                    ·
                      refine ⟨3935307520367647861053985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20988306775294121925621253 3935307520367647861053985)
                      ·
                        rfl

theorem cell23_7663984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 4].length) (baseStart_7663984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7663984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7663984 prefixEnd_7663984 := by exact prefixLift 7663984
  have htrace : WordTrace (prefixWord ++ tailWord_7663984) baseStart_7663984 baseEnd_7663984 := by
    simpa [prefixWord, tailWord_7663984, baseEnd_7663984] using wordTrace_append hprefix tailTrace_7663984
  have hstable : (prefixWord ++ tailWord_7663984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7663984).length < 2 ^ (prefixWord ++ tailWord_7663984).sum := by decide
  have hdescent : baseEnd_7663984 < baseStart_7663984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7663984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664004 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_7664004 : Nat := 118140960795 + 7664004 * 2 ^ 59
def prefixEnd_7664004 : Nat := 4983230072969 + 3 ^ 40 * 7664004 * 2
def baseEnd_7664004 : Nat := 3935317789980737782803893

theorem tailTrace_7664004 : CollatzResearch.WordTrace tailWord_7664004 prefixEnd_7664004 3935317789980737782803893 := by
  unfold tailWord_7664004
  simp only [CollatzResearch.WordTrace]
  refine ⟨139764595063314945260423533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186352793417753260347231377 139764595063314945260423533)
  ·
    refine ⟨52411723148743104472658825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139764595063314945260423533 52411723148743104472658825)
    ·
      refine ⟨39308792361557328354494119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52411723148743104472658825 39308792361557328354494119)
      ·
        refine ⟨58963188542335992531741179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39308792361557328354494119 58963188542335992531741179)
        ·
          refine ⟨88444782813503988797611769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58963188542335992531741179 88444782813503988797611769)
          ·
            refine ⟨66333587110127991598208827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88444782813503988797611769 66333587110127991598208827)
            ·
              refine ⟨99500380665191987397313241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66333587110127991598208827 99500380665191987397313241)
              ·
                refine ⟨74625285498893990547984931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99500380665191987397313241 74625285498893990547984931)
                ·
                  refine ⟨111937928248340985821977397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74625285498893990547984931 111937928248340985821977397)
                  ·
                    refine ⟨10494180773281967420810381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111937928248340985821977397 10494180773281967420810381)
                    ·
                      refine ⟨3935317789980737782803893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10494180773281967420810381 3935317789980737782803893)
                      ·
                        rfl

theorem cell23_7664004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_7664004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664004 prefixEnd_7664004 := by exact prefixLift 7664004
  have htrace : WordTrace (prefixWord ++ tailWord_7664004) baseStart_7664004 baseEnd_7664004 := by
    simpa [prefixWord, tailWord_7664004, baseEnd_7664004] using wordTrace_append hprefix tailTrace_7664004
  have hstable : (prefixWord ++ tailWord_7664004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664004).length < 2 ^ (prefixWord ++ tailWord_7664004).sum := by decide
  have hdescent : baseEnd_7664004 < baseStart_7664004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664011 : List Nat := [1, 1, 1, 1, 4, 5, 2, 3, 5]
def baseStart_7664011 : Nat := 118140960795 + 7664011 * 2 ^ 59
def prefixEnd_7664011 : Nat := 4983230072969 + 3 ^ 40 * 7664011 * 2
def baseEnd_7664011 : Nat := 437257931593924361712929

theorem tailTrace_7664011 : CollatzResearch.WordTrace tailWord_7664011 prefixEnd_7664011 437257931593924361712929 := by
  unfold tailWord_7664011
  simp only [CollatzResearch.WordTrace]
  refine ⟨279529445437604530716351887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186352963625069687144234591 279529445437604530716351887)
  ·
    refine ⟨419294168156406796074527831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279529445437604530716351887 419294168156406796074527831)
    ·
      refine ⟨628941252234610194111791747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419294168156406796074527831 628941252234610194111791747)
      ·
        refine ⟨943411878351915291167687621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628941252234610194111791747 943411878351915291167687621)
        ·
          refine ⟨176889727190984117093941429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 943411878351915291167687621 176889727190984117093941429)
          ·
            refine ⟨16583411924154760977557009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176889727190984117093941429 16583411924154760977557009)
            ·
              refine ⟨12437558943116070733167757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16583411924154760977557009 12437558943116070733167757)
              ·
                refine ⟨4664084603668526524937909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12437558943116070733167757 4664084603668526524937909)
                ·
                  refine ⟨437257931593924361712929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4664084603668526524937909 437257931593924361712929)
                  ·
                    rfl

theorem cell23_7664011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 5].length) (baseStart_7664011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664011 prefixEnd_7664011 := by exact prefixLift 7664011
  have htrace : WordTrace (prefixWord ++ tailWord_7664011) baseStart_7664011 baseEnd_7664011 := by
    simpa [prefixWord, tailWord_7664011, baseEnd_7664011] using wordTrace_append hprefix tailTrace_7664011
  have hstable : (prefixWord ++ tailWord_7664011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664011).length < 2 ^ (prefixWord ++ tailWord_7664011).sum := by decide
  have hdescent : baseEnd_7664011 < baseStart_7664011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664034 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_7664034 : Nat := 118140960795 + 7664034 * 2 ^ 59
def prefixEnd_7664034 : Nat := 4983230072969 + 3 ^ 40 * 7664034 * 2
def baseEnd_7664034 : Nat := 3935333194400372665428755

theorem tailTrace_7664034 : CollatzResearch.WordTrace tailWord_7664034 prefixEnd_7664034 3935333194400372665428755 := by
  unfold tailWord_7664034
  simp only [CollatzResearch.WordTrace]
  refine ⟨69882571079130301411109789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186353522877680803762959437 69882571079130301411109789)
  ·
    refine ⟨26205964154673863029166171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69882571079130301411109789 26205964154673863029166171)
    ·
      refine ⟨39308946232010794543749257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26205964154673863029166171 39308946232010794543749257)
      ·
        refine ⟨29481709674008095907811943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39308946232010794543749257 29481709674008095907811943)
        ·
          refine ⟨44222564511012143861717915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29481709674008095907811943 44222564511012143861717915)
          ·
            refine ⟨66333846766518215792576873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44222564511012143861717915 66333846766518215792576873)
            ·
              refine ⟨49750385074888661844432655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66333846766518215792576873 49750385074888661844432655)
              ·
                refine ⟨74625577612332992766648983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49750385074888661844432655 74625577612332992766648983)
                ·
                  refine ⟨111938366418499489149973475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74625577612332992766648983 111938366418499489149973475)
                  ·
                    refine ⟨167907549627749233724960213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111938366418499489149973475 167907549627749233724960213)
                    ·
                      refine ⟨3935333194400372665428755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167907549627749233724960213 3935333194400372665428755)
                      ·
                        rfl

theorem cell23_7664034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_7664034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664034 prefixEnd_7664034 := by exact prefixLift 7664034
  have htrace : WordTrace (prefixWord ++ tailWord_7664034) baseStart_7664034 baseEnd_7664034 := by
    simpa [prefixWord, tailWord_7664034, baseEnd_7664034] using wordTrace_append hprefix tailTrace_7664034
  have hstable : (prefixWord ++ tailWord_7664034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664034).length < 2 ^ (prefixWord ++ tailWord_7664034).sum := by decide
  have hdescent : baseEnd_7664034 < baseStart_7664034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664111 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 5, 1, 3]
def baseStart_7664111 : Nat := 118140960795 + 7664111 * 2 ^ 59
def prefixEnd_7664111 : Nat := 4983230072969 + 3 ^ 40 * 7664111 * 2
def baseEnd_7664111 : Nat := 3935372732410768864165901

theorem tailTrace_7664111 : CollatzResearch.WordTrace tailWord_7664111 prefixEnd_7664111 3935372732410768864165901 := by
  unfold tailWord_7664111
  simp only [CollatzResearch.WordTrace]
  refine ⟨279533092737242247794992187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186355395158161498529994791 279533092737242247794992187)
  ·
    refine ⟨419299639105863371692488281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279533092737242247794992187 419299639105863371692488281)
    ·
      refine ⟨314474729329397528769366211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419299639105863371692488281 314474729329397528769366211)
      ·
        refine ⟨471712093994096293154049317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314474729329397528769366211 471712093994096293154049317)
        ·
          refine ⟨88446017623893054966384247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 471712093994096293154049317 88446017623893054966384247)
          ·
            refine ⟨132669026435839582449576371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88446017623893054966384247 132669026435839582449576371)
            ·
              refine ⟨199003539653759373674364557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132669026435839582449576371 199003539653759373674364557)
              ·
                refine ⟨74626327370159765127886709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199003539653759373674364557 74626327370159765127886709)
                ·
                  refine ⟨6996218190952477980739379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74626327370159765127886709 6996218190952477980739379)
                  ·
                    refine ⟨10494327286428716971109069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6996218190952477980739379 10494327286428716971109069)
                    ·
                      refine ⟨3935372732410768864165901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10494327286428716971109069 3935372732410768864165901)
                      ·
                        rfl

theorem cell23_7664111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 1, 3].length) (baseStart_7664111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664111 prefixEnd_7664111 := by exact prefixLift 7664111
  have htrace : WordTrace (prefixWord ++ tailWord_7664111) baseStart_7664111 baseEnd_7664111 := by
    simpa [prefixWord, tailWord_7664111, baseEnd_7664111] using wordTrace_append hprefix tailTrace_7664111
  have hstable : (prefixWord ++ tailWord_7664111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664111).length < 2 ^ (prefixWord ++ tailWord_7664111).sum := by decide
  have hdescent : baseEnd_7664111 < baseStart_7664111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664121 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 1, 5, 2]
def baseStart_7664121 : Nat := 118140960795 + 7664121 * 2 ^ 59
def prefixEnd_7664121 : Nat := 4983230072969 + 3 ^ 40 * 7664121 * 2
def baseEnd_7664121 : Nat := 3935377867217313825040855

theorem tailTrace_7664121 : CollatzResearch.WordTrace tailWord_7664121 prefixEnd_7664121 3935377867217313825040855 := by
  unfold tailWord_7664121
  simp only [CollatzResearch.WordTrace]
  refine ⟨279533457467206019502856217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186355638311470679668570811 279533457467206019502856217)
  ·
    refine ⟨209650093100404514627142163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279533457467206019502856217 209650093100404514627142163)
    ·
      refine ⟨314475139650606771940713245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209650093100404514627142163 314475139650606771940713245)
      ·
        refine ⟨117928177368977539477767467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314475139650606771940713245 117928177368977539477767467)
        ·
          refine ⟨176892266053466309216651201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117928177368977539477767467 176892266053466309216651201)
          ·
            refine ⟨132669199540099731912488401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176892266053466309216651201 132669199540099731912488401)
            ·
              refine ⟨99501899655074798934366301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132669199540099731912488401 99501899655074798934366301)
              ·
                refine ⟨37313212370653049600387363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99501899655074798934366301 37313212370653049600387363)
                ·
                  refine ⟨55969818555979574400581045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37313212370653049600387363 55969818555979574400581045)
                  ·
                    refine ⟨5247170489623085100054473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55969818555979574400581045 5247170489623085100054473)
                    ·
                      refine ⟨3935377867217313825040855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5247170489623085100054473 3935377867217313825040855)
                      ·
                        rfl

theorem cell23_7664121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_7664121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664121 prefixEnd_7664121 := by exact prefixLift 7664121
  have htrace : WordTrace (prefixWord ++ tailWord_7664121) baseStart_7664121 baseEnd_7664121 := by
    simpa [prefixWord, tailWord_7664121, baseEnd_7664121] using wordTrace_append hprefix tailTrace_7664121
  have hstable : (prefixWord ++ tailWord_7664121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664121).length < 2 ^ (prefixWord ++ tailWord_7664121).sum := by decide
  have hdescent : baseEnd_7664121 < baseStart_7664121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664138 : List Nat := [3, 1, 2, 2, 2, 1, 1, 4, 2, 3, 2]
def baseStart_7664138 : Nat := 118140960795 + 7664138 * 2 ^ 59
def prefixEnd_7664138 : Nat := 4983230072969 + 3 ^ 40 * 7664138 * 2
def baseEnd_7664138 : Nat := 3935386596388440258528277

theorem tailTrace_7664138 : CollatzResearch.WordTrace tailWord_7664138 prefixEnd_7664138 3935386596388440258528277 := by
  unfold tailWord_7664138
  simp only [CollatzResearch.WordTrace]
  refine ⟨69883519377036107851556267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186356051672096287604150045 69883519377036107851556267)
  ·
    refine ⟨104825279065554161777334401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69883519377036107851556267 104825279065554161777334401)
    ·
      refine ⟨78618959299165621333000801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104825279065554161777334401 78618959299165621333000801)
      ·
        refine ⟨58964219474374215999750601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78618959299165621333000801 58964219474374215999750601)
        ·
          refine ⟨44223164605780661999812951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58964219474374215999750601 44223164605780661999812951)
          ·
            refine ⟨66334746908670992999719427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44223164605780661999812951 66334746908670992999719427)
            ·
              refine ⟨99502120363006489499579141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66334746908670992999719427 99502120363006489499579141)
              ·
                refine ⟨18656647568063716781171089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99502120363006489499579141 18656647568063716781171089)
                ·
                  refine ⟨13992485676047787585878317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18656647568063716781171089 13992485676047787585878317)
                  ·
                    refine ⟨5247182128517920344704369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13992485676047787585878317 5247182128517920344704369)
                    ·
                      refine ⟨3935386596388440258528277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5247182128517920344704369 3935386596388440258528277)
                      ·
                        rfl

theorem cell23_7664138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_7664138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664138 prefixEnd_7664138 := by exact prefixLift 7664138
  have htrace : WordTrace (prefixWord ++ tailWord_7664138) baseStart_7664138 baseEnd_7664138 := by
    simpa [prefixWord, tailWord_7664138, baseEnd_7664138] using wordTrace_append hprefix tailTrace_7664138
  have hstable : (prefixWord ++ tailWord_7664138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664138).length < 2 ^ (prefixWord ++ tailWord_7664138).sum := by decide
  have hdescent : baseEnd_7664138 < baseStart_7664138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664148 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_7664148 : Nat := 118140960795 + 7664148 * 2 ^ 59
def prefixEnd_7664148 : Nat := 4983230072969 + 3 ^ 40 * 7664148 * 2
def baseEnd_7664148 : Nat := 1311797243731661739801077

theorem tailTrace_7664148 : CollatzResearch.WordTrace tailWord_7664148 prefixEnd_7664148 1311797243731661739801077 := by
  unfold tailWord_7664148
  simp only [CollatzResearch.WordTrace]
  refine ⟨139767221119054101557044549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186356294825405468742726065 139767221119054101557044549)
  ·
    refine ⟨26206353959822644041945853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139767221119054101557044549 26206353959822644041945853)
    ·
      refine ⟨9827382734933491515729695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26206353959822644041945853 9827382734933491515729695)
      ·
        refine ⟨14741074102400237273594543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9827382734933491515729695 14741074102400237273594543)
        ·
          refine ⟨22111611153600355910391815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14741074102400237273594543 22111611153600355910391815)
          ·
            refine ⟨33167416730400533865587723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22111611153600355910391815 33167416730400533865587723)
            ·
              refine ⟨49751125095600800798381585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33167416730400533865587723 49751125095600800798381585)
              ·
                refine ⟨37313343821700600598786189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49751125095600800798381585 37313343821700600598786189)
                ·
                  refine ⟨13992503933137725224544821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37313343821700600598786189 13992503933137725224544821)
                  ·
                    refine ⟨1311797243731661739801077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13992503933137725224544821 1311797243731661739801077)
                    ·
                      rfl

theorem cell23_7664148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_7664148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664148 prefixEnd_7664148 := by exact prefixLift 7664148
  have htrace : WordTrace (prefixWord ++ tailWord_7664148) baseStart_7664148 baseEnd_7664148 := by
    simpa [prefixWord, tailWord_7664148, baseEnd_7664148] using wordTrace_append hprefix tailTrace_7664148
  have hstable : (prefixWord ++ tailWord_7664148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664148).length < 2 ^ (prefixWord ++ tailWord_7664148).sum := by decide
  have hdescent : baseEnd_7664148 < baseStart_7664148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664161 : List Nat := [1, 2, 3, 2, 2, 1, 4, 1, 1, 6]
def baseStart_7664161 : Nat := 118140960795 + 7664161 * 2 ^ 59
def prefixEnd_7664161 : Nat := 4983230072969 + 3 ^ 40 * 7664161 * 2
def baseEnd_7664161 : Nat := 1311799468814497889513557

theorem tailTrace_7664161 : CollatzResearch.WordTrace tailWord_7664161 prefixEnd_7664161 1311799468814497889513557 := by
  unfold tailWord_7664161
  simp only [CollatzResearch.WordTrace]
  refine ⟨279534916387061106334312337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186356610924707404222874891 279534916387061106334312337)
  ·
    refine ⟨209651187290295829750734253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279534916387061106334312337 209651187290295829750734253)
    ·
      refine ⟨78619195233860936156525345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209651187290295829750734253 78619195233860936156525345)
      ·
        refine ⟨58964396425395702117394009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78619195233860936156525345 58964396425395702117394009)
        ·
          refine ⟨44223297319046776588045507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58964396425395702117394009 44223297319046776588045507)
          ·
            refine ⟨66334945978570164882068261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44223297319046776588045507 66334945978570164882068261)
            ·
              refine ⟨12437802370981905915387799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66334945978570164882068261 12437802370981905915387799)
              ·
                refine ⟨18656703556472858873081699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12437802370981905915387799 18656703556472858873081699)
                ·
                  refine ⟨27985055334709288309622549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18656703556472858873081699 27985055334709288309622549)
                  ·
                    refine ⟨1311799468814497889513557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27985055334709288309622549 1311799468814497889513557)
                    ·
                      rfl

theorem cell23_7664161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_7664161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664161 prefixEnd_7664161 := by exact prefixLift 7664161
  have htrace : WordTrace (prefixWord ++ tailWord_7664161) baseStart_7664161 baseEnd_7664161 := by
    simpa [prefixWord, tailWord_7664161, baseEnd_7664161] using wordTrace_append hprefix tailTrace_7664161
  have hstable : (prefixWord ++ tailWord_7664161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664161).length < 2 ^ (prefixWord ++ tailWord_7664161).sum := by decide
  have hdescent : baseEnd_7664161 < baseStart_7664161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664168 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_7664168 : Nat := 118140960795 + 7664168 * 2 ^ 59
def prefixEnd_7664168 : Nat := 4983230072969 + 3 ^ 40 * 7664168 * 2
def baseEnd_7664168 : Nat := 3935402000808075141153139

theorem tailTrace_7664168 : CollatzResearch.WordTrace tailWord_7664168 prefixEnd_7664168 3935402000808075141153139 := by
  unfold tailWord_7664168
  simp only [CollatzResearch.WordTrace]
  refine ⟨139767585849017873264908579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186356781132023831019878105 139767585849017873264908579)
  ·
    refine ⟨209651378773526809897362869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139767585849017873264908579 209651378773526809897362869)
    ·
      refine ⟨19654816760018138427877769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209651378773526809897362869 19654816760018138427877769)
      ·
        refine ⟨14741112570013603820908327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19654816760018138427877769 14741112570013603820908327)
        ·
          refine ⟨22111668855020405731362491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14741112570013603820908327 22111668855020405731362491)
          ·
            refine ⟨33167503282530608597043737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22111668855020405731362491 33167503282530608597043737)
            ·
              refine ⟨24875627461897956447782803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33167503282530608597043737 24875627461897956447782803)
              ·
                refine ⟨37313441192846934671674205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24875627461897956447782803 37313441192846934671674205)
                ·
                  refine ⟨13992540447317600501877827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37313441192846934671674205 13992540447317600501877827)
                  ·
                    refine ⟨20988810670976400752816741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13992540447317600501877827 20988810670976400752816741)
                    ·
                      refine ⟨3935402000808075141153139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20988810670976400752816741 3935402000808075141153139)
                      ·
                        rfl

theorem cell23_7664168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_7664168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664168 prefixEnd_7664168 := by exact prefixLift 7664168
  have htrace : WordTrace (prefixWord ++ tailWord_7664168) baseStart_7664168 baseEnd_7664168 := by
    simpa [prefixWord, tailWord_7664168, baseEnd_7664168] using wordTrace_append hprefix tailTrace_7664168
  have hstable : (prefixWord ++ tailWord_7664168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664168).length < 2 ^ (prefixWord ++ tailWord_7664168).sum := by decide
  have hdescent : baseEnd_7664168 < baseStart_7664168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664181 : List Nat := [1, 3, 3, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_7664181 : Nat := 118140960795 + 7664181 * 2 ^ 59
def prefixEnd_7664181 : Nat := 4983230072969 + 3 ^ 40 * 7664181 * 2
def baseEnd_7664181 : Nat := 3935408676056583590290579

theorem tailTrace_7664181 : CollatzResearch.WordTrace tailWord_7664181 prefixEnd_7664181 3935408676056583590290579 := by
  unfold tailWord_7664181
  simp only [CollatzResearch.WordTrace]
  refine ⟨279535645846988649750040397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186357097231325766500026931 279535645846988649750040397)
  ·
    refine ⟨104825867192620743656265149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279535645846988649750040397 104825867192620743656265149)
    ·
      refine ⟨39309700197232778871099431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104825867192620743656265149 39309700197232778871099431)
      ·
        refine ⟨58964550295849168306649147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39309700197232778871099431 58964550295849168306649147)
        ·
          refine ⟨88446825443773752459973721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58964550295849168306649147 88446825443773752459973721)
          ·
            refine ⟨66335119082830314344980291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88446825443773752459973721 66335119082830314344980291)
            ·
              refine ⟨99502678624245471517470437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66335119082830314344980291 99502678624245471517470437)
              ·
                refine ⟨18656752242046025909525707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99502678624245471517470437 18656752242046025909525707)
                ·
                  refine ⟨27985128363069038864288561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18656752242046025909525707 27985128363069038864288561)
                  ·
                    refine ⟨20988846272301779148216421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27985128363069038864288561 20988846272301779148216421)
                    ·
                      refine ⟨3935408676056583590290579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20988846272301779148216421 3935408676056583590290579)
                      ·
                        rfl

theorem cell23_7664181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_7664181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664181 prefixEnd_7664181 := by exact prefixLift 7664181
  have htrace : WordTrace (prefixWord ++ tailWord_7664181) baseStart_7664181 baseEnd_7664181 := by
    simpa [prefixWord, tailWord_7664181, baseEnd_7664181] using wordTrace_append hprefix tailTrace_7664181
  have hstable : (prefixWord ++ tailWord_7664181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664181).length < 2 ^ (prefixWord ++ tailWord_7664181).sum := by decide
  have hdescent : baseEnd_7664181 < baseStart_7664181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7664182 : List Nat := [5, 1, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_7664182 : Nat := 118140960795 + 7664182 * 2 ^ 59
def prefixEnd_7664182 : Nat := 4983230072969 + 3 ^ 40 * 7664182 * 2
def baseEnd_7664182 : Nat := 1311803063179079362126025

theorem tailTrace_7664182 : CollatzResearch.WordTrace tailWord_7664182 prefixEnd_7664182 1311803063179079362126025 := by
  unfold tailWord_7664182
  simp only [CollatzResearch.WordTrace]
  refine ⟨17470980144999064182551675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186357121546656684613884533 17470980144999064182551675)
  ·
    refine ⟨26206470217498596273827513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17470980144999064182551675 26206470217498596273827513)
    ·
      refine ⟨19654852663123947205370635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26206470217498596273827513 19654852663123947205370635)
      ·
        refine ⟨29482278994685920808055953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19654852663123947205370635 29482278994685920808055953)
        ·
          refine ⟨22111709246014440606041965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29482278994685920808055953 22111709246014440606041965)
          ·
            refine ⟨8291890967255415227265737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22111709246014440606041965 8291890967255415227265737)
            ·
              refine ⟨6218918225441561420449303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8291890967255415227265737 6218918225441561420449303)
              ·
                refine ⟨9328377338162342130673955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6218918225441561420449303 9328377338162342130673955)
                ·
                  refine ⟨13992566007243513196010933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9328377338162342130673955 13992566007243513196010933)
                  ·
                    refine ⟨1311803063179079362126025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13992566007243513196010933 1311803063179079362126025)
                    ·
                      rfl

theorem cell23_7664182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_7664182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7664182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7664182 prefixEnd_7664182 := by exact prefixLift 7664182
  have htrace : WordTrace (prefixWord ++ tailWord_7664182) baseStart_7664182 baseEnd_7664182 := by
    simpa [prefixWord, tailWord_7664182, baseEnd_7664182] using wordTrace_append hprefix tailTrace_7664182
  have hstable : (prefixWord ++ tailWord_7664182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7664182).length < 2 ^ (prefixWord ++ tailWord_7664182).sum := by decide
  have hdescent : baseEnd_7664182 < baseStart_7664182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7664182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
