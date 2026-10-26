import V185TrunkScan19Chunk025

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_259772 : List Nat := [2, 2, 2, 3, 1, 2, 1, 6]
def baseStart_259772 : Nat := 118140960795 + 259772 * 2 ^ 59
def prefixEnd_259772 : Nat := 4983230072969 + 3 ^ 40 * 259772 * 2
def baseEnd_259772 : Nat := 79044679454733555292051

theorem tailTrace_259772 : CollatzResearch.WordTrace tailWord_259772 prefixEnd_259772 79044679454733555292051 := by
  unfold tailWord_259772
  simp only [CollatzResearch.WordTrace]
  refine ⟨4737331607448942185294785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6316442143265256247059713 4737331607448942185294785)
  ·
    refine ⟨3552998705586706638971089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4737331607448942185294785 3552998705586706638971089)
    ·
      refine ⟨2664749029190029979228317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3552998705586706638971089 2664749029190029979228317)
      ·
        refine ⟨999280885946261242210619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2664749029190029979228317 999280885946261242210619)
        ·
          refine ⟨1498921328919391863315929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999280885946261242210619 1498921328919391863315929)
          ·
            refine ⟨1124190996689543897486947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1498921328919391863315929 1124190996689543897486947)
            ·
              refine ⟨1686286495034315846230421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124190996689543897486947 1686286495034315846230421)
              ·
                refine ⟨79044679454733555292051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1686286495034315846230421 79044679454733555292051)
                ·
                  rfl

theorem cell19_259772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_259772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259772 prefixEnd_259772 := by exact prefixLift 259772
  have htrace : WordTrace (prefixWord ++ tailWord_259772) baseStart_259772 baseEnd_259772 := by
    simpa [prefixWord, tailWord_259772, baseEnd_259772] using wordTrace_append hprefix tailTrace_259772
  have hstable : (prefixWord ++ tailWord_259772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259772).length < 2 ^ (prefixWord ++ tailWord_259772).sum := by decide
  have hdescent : baseEnd_259772 < baseStart_259772 := by decide
  rcases family_descends (prefixWord ++ tailWord_259772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259901 : List Nat := [1, 4, 1, 4, 1, 3, 2, 3]
def baseStart_259901 : Nat := 118140960795 + 259901 * 2 ^ 59
def prefixEnd_259901 : Nat := 4983230072969 + 3 ^ 40 * 259901 * 2
def baseEnd_259901 : Nat := 79083932198099478425033

theorem tailTrace_259901 : CollatzResearch.WordTrace tailWord_259901 prefixEnd_259901 79083932198099478425033 := by
  unfold tailWord_259901
  simp only [CollatzResearch.WordTrace]
  refine ⟨9479368231430539402035557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6319578820953692934690371 9479368231430539402035557)
  ·
    refine ⟨1777381543393226137881667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9479368231430539402035557 1777381543393226137881667)
    ·
      refine ⟨2666072315089839206822501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1777381543393226137881667 2666072315089839206822501)
      ·
        refine ⟨499888559079344851279219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2666072315089839206822501 499888559079344851279219)
        ·
          refine ⟨749832838619017276918829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499888559079344851279219 749832838619017276918829)
          ·
            refine ⟨281187314482131478844561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 749832838619017276918829 281187314482131478844561)
            ·
              refine ⟨210890485861598609133421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281187314482131478844561 210890485861598609133421)
              ·
                refine ⟨79083932198099478425033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210890485861598609133421 79083932198099478425033)
                ·
                  rfl

theorem cell19_259901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 3].length) (baseStart_259901 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259901 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259901 prefixEnd_259901 := by exact prefixLift 259901
  have htrace : WordTrace (prefixWord ++ tailWord_259901) baseStart_259901 baseEnd_259901 := by
    simpa [prefixWord, tailWord_259901, baseEnd_259901] using wordTrace_append hprefix tailTrace_259901
  have hstable : (prefixWord ++ tailWord_259901).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259901).length < 2 ^ (prefixWord ++ tailWord_259901).sum := by decide
  have hdescent : baseEnd_259901 < baseStart_259901 := by decide
  rcases family_descends (prefixWord ++ tailWord_259901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259924 : List Nat := [2, 4, 1, 1, 3, 1, 7]
def baseStart_259924 : Nat := 118140960795 + 259924 * 2 ^ 59
def prefixEnd_259924 : Nat := 4983230072969 + 3 ^ 40 * 259924 * 2
def baseEnd_259924 : Nat := 26363643583080746637953

theorem tailTrace_259924 : CollatzResearch.WordTrace tailWord_259924 prefixEnd_259924 26363643583080746637953 := by
  unfold tailWord_259924
  simp only [CollatzResearch.WordTrace]
  refine ⟨4740103555173607165061413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6320138073564809553415217 4740103555173607165061413)
  ·
    refine ⟨888769416595051343449015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4740103555173607165061413 888769416595051343449015)
    ·
      refine ⟨1333154124892577015173523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 888769416595051343449015 1333154124892577015173523)
      ·
        refine ⟨1999731187338865522760285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1333154124892577015173523 1999731187338865522760285)
        ·
          refine ⟨749899195252074571035107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1999731187338865522760285 749899195252074571035107)
          ·
            refine ⟨1124848792878111856552661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749899195252074571035107 1124848792878111856552661)
            ·
              refine ⟨26363643583080746637953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1124848792878111856552661 26363643583080746637953)
              ·
                rfl

theorem cell19_259924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 7].length) (baseStart_259924 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259924 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259924 prefixEnd_259924 := by exact prefixLift 259924
  have htrace : WordTrace (prefixWord ++ tailWord_259924) baseStart_259924 baseEnd_259924 := by
    simpa [prefixWord, tailWord_259924, baseEnd_259924] using wordTrace_append hprefix tailTrace_259924
  have hstable : (prefixWord ++ tailWord_259924).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259924).length < 2 ^ (prefixWord ++ tailWord_259924).sum := by decide
  have hdescent : baseEnd_259924 < baseStart_259924 := by decide
  rcases family_descends (prefixWord ++ tailWord_259924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259943 : List Nat := [1, 1, 5, 1, 2, 1, 4, 4]
def baseStart_259943 : Nat := 118140960795 + 259943 * 2 ^ 59
def prefixEnd_259943 : Nat := 4983230072969 + 3 ^ 40 * 259943 * 2
def baseEnd_259943 : Nat := 79096712161055825491585

theorem tailTrace_259943 : CollatzResearch.WordTrace tailWord_259943 prefixEnd_259943 79096712161055825491585 := by
  unfold tailWord_259943
  simp only [CollatzResearch.WordTrace]
  refine ⟨9480900097278380575064483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6320600064852253716709655 9480900097278380575064483)
  ·
    refine ⟨14221350145917570862596725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9480900097278380575064483 14221350145917570862596725)
    ·
      refine ⟨1333251576179772268368443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14221350145917570862596725 1333251576179772268368443)
      ·
        refine ⟨1999877364269658402552665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1333251576179772268368443 1999877364269658402552665)
        ·
          refine ⟨1499908023202243801914499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1999877364269658402552665 1499908023202243801914499)
          ·
            refine ⟨2249862034803365702871749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499908023202243801914499 2249862034803365702871749)
            ·
              refine ⟨421849131525631069288453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2249862034803365702871749 421849131525631069288453)
              ·
                refine ⟨79096712161055825491585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 421849131525631069288453 79096712161055825491585)
                ·
                  rfl

theorem cell19_259943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_259943 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259943 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259943 prefixEnd_259943 := by exact prefixLift 259943
  have htrace : WordTrace (prefixWord ++ tailWord_259943) baseStart_259943 baseEnd_259943 := by
    simpa [prefixWord, tailWord_259943, baseEnd_259943] using wordTrace_append hprefix tailTrace_259943
  have hstable : (prefixWord ++ tailWord_259943).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259943).length < 2 ^ (prefixWord ++ tailWord_259943).sum := by decide
  have hdescent : baseEnd_259943 < baseStart_259943 := by decide
  rcases family_descends (prefixWord ++ tailWord_259943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260017 : List Nat := [1, 2, 2, 4, 2, 2, 3, 3]
def baseStart_260017 : Nat := 118140960795 + 260017 * 2 ^ 59
def prefixEnd_260017 : Nat := 4983230072969 + 3 ^ 40 * 260017 * 2
def baseEnd_260017 : Nat := 79119229238645579846939

theorem tailTrace_260017 : CollatzResearch.WordTrace tailWord_260017 prefixEnd_260017 79119229238645579846939 := by
  unfold tailWord_260017
  simp only [CollatzResearch.WordTrace]
  refine ⟨9483599099010291213258305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6322399399340194142172203 9483599099010291213258305)
  ·
    refine ⟨7112699324257718409943729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9483599099010291213258305 7112699324257718409943729)
    ·
      refine ⟨5334524493193288807457797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7112699324257718409943729 5334524493193288807457797)
      ·
        refine ⟨1000223342473741651398337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5334524493193288807457797 1000223342473741651398337)
        ·
          refine ⟨750167506855306238548753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1000223342473741651398337 750167506855306238548753)
          ·
            refine ⟨562625630141479678911565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 750167506855306238548753 562625630141479678911565)
            ·
              refine ⟨210984611303054879591837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 562625630141479678911565 210984611303054879591837)
              ·
                refine ⟨79119229238645579846939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210984611303054879591837 79119229238645579846939)
                ·
                  rfl

theorem cell19_260017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 3].length) (baseStart_260017 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260017 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260017 prefixEnd_260017 := by exact prefixLift 260017
  have htrace : WordTrace (prefixWord ++ tailWord_260017) baseStart_260017 baseEnd_260017 := by
    simpa [prefixWord, tailWord_260017, baseEnd_260017] using wordTrace_append hprefix tailTrace_260017
  have hstable : (prefixWord ++ tailWord_260017).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260017).length < 2 ^ (prefixWord ++ tailWord_260017).sum := by decide
  have hdescent : baseEnd_260017 < baseStart_260017 := by decide
  rcases family_descends (prefixWord ++ tailWord_260017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260019 : List Nat := [1, 1, 1, 2, 3, 1, 7, 3]
def baseStart_260019 : Nat := 118140960795 + 260019 * 2 ^ 59
def prefixEnd_260019 : Nat := 4983230072969 + 3 ^ 40 * 260019 * 2
def baseEnd_260019 : Nat := 79119837808310167802489

theorem tailTrace_260019 : CollatzResearch.WordTrace tailWord_260019 prefixEnd_260019 79119837808310167802489 := by
  unfold tailWord_260019
  simp only [CollatzResearch.WordTrace]
  refine ⟨9483672045003045554831111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6322448030002030369887407 9483672045003045554831111)
  ·
    refine ⟨14225508067504568332246667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9483672045003045554831111 14225508067504568332246667)
    ·
      refine ⟨21338262101256852498370001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14225508067504568332246667 21338262101256852498370001)
      ·
        refine ⟨16003696575942639373777501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21338262101256852498370001 16003696575942639373777501)
        ·
          refine ⟨6001386215978489765166563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16003696575942639373777501 6001386215978489765166563)
          ·
            refine ⟨9002079323967734647749845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6001386215978489765166563 9002079323967734647749845)
            ·
              refine ⟨210986234155493780806637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9002079323967734647749845 210986234155493780806637)
              ·
                refine ⟨79119837808310167802489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210986234155493780806637 79119837808310167802489)
                ·
                  rfl

theorem cell19_260019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 3].length) (baseStart_260019 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260019 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260019 prefixEnd_260019 := by exact prefixLift 260019
  have htrace : WordTrace (prefixWord ++ tailWord_260019) baseStart_260019 baseEnd_260019 := by
    simpa [prefixWord, tailWord_260019, baseEnd_260019] using wordTrace_append hprefix tailTrace_260019
  have hstable : (prefixWord ++ tailWord_260019).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260019).length < 2 ^ (prefixWord ++ tailWord_260019).sum := by decide
  have hdescent : baseEnd_260019 < baseStart_260019 := by decide
  rcases family_descends (prefixWord ++ tailWord_260019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260152 : List Nat := [2, 1, 2, 1, 7, 6]
def baseStart_260152 : Nat := 118140960795 + 260152 * 2 ^ 59
def prefixEnd_260152 : Nat := 4983230072969 + 3 ^ 40 * 260152 * 2
def baseEnd_260152 : Nat := 8795589743445029649619

theorem tailTrace_260152 : CollatzResearch.WordTrace tailWord_260152 prefixEnd_260152 8795589743445029649619 := by
  unfold tailWord_260152
  simp only [CollatzResearch.WordTrace]
  refine ⟨4744261476760604634711355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6325681969014139512948473 4744261476760604634711355)
  ·
    refine ⟨7116392215140906952067033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4744261476760604634711355 7116392215140906952067033)
    ·
      refine ⟨5337294161355680214050275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7116392215140906952067033 5337294161355680214050275)
      ·
        refine ⟨8005941242033520321075413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5337294161355680214050275 8005941242033520321075413)
        ·
          refine ⟨187639247860160632525205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 8005941242033520321075413 187639247860160632525205)
          ·
            refine ⟨8795589743445029649619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187639247860160632525205 8795589743445029649619)
            ·
              rfl

theorem cell19_260152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 6].length) (baseStart_260152 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260152 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260152 prefixEnd_260152 := by exact prefixLift 260152
  have htrace : WordTrace (prefixWord ++ tailWord_260152) baseStart_260152 baseEnd_260152 := by
    simpa [prefixWord, tailWord_260152, baseEnd_260152] using wordTrace_append hprefix tailTrace_260152
  have hstable : (prefixWord ++ tailWord_260152).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260152).length < 2 ^ (prefixWord ++ tailWord_260152).sum := by decide
  have hdescent : baseEnd_260152 < baseStart_260152 := by decide
  rcases family_descends (prefixWord ++ tailWord_260152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260188 : List Nat := [2, 2, 4, 1, 1, 3, 3, 3]
def baseStart_260188 : Nat := 118140960795 + 260188 * 2 ^ 59
def prefixEnd_260188 : Nat := 4983230072969 + 3 ^ 40 * 260188 * 2
def baseEnd_260188 : Nat := 79171261944967850046473

theorem tailTrace_260188 : CollatzResearch.WordTrace tailWord_260188 prefixEnd_260188 79171261944967850046473 := by
  unfold tailWord_260188
  simp only [CollatzResearch.WordTrace]
  refine ⟨4744917990695393708866609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6326557320927191611822145 4744917990695393708866609)
  ·
    refine ⟨3558688493021545281649957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4744917990695393708866609 3558688493021545281649957)
    ·
      refine ⟨667254092441539740309367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3558688493021545281649957 667254092441539740309367)
      ·
        refine ⟨1000881138662309610464051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667254092441539740309367 1000881138662309610464051)
        ·
          refine ⟨1501321707993464415696077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1000881138662309610464051 1501321707993464415696077)
          ·
            refine ⟨562995640497549155886029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1501321707993464415696077 562995640497549155886029)
            ·
              refine ⟨211123365186580933457261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 562995640497549155886029 211123365186580933457261)
              ·
                refine ⟨79171261944967850046473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211123365186580933457261 79171261944967850046473)
                ·
                  rfl

theorem cell19_260188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_260188 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260188 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260188 prefixEnd_260188 := by exact prefixLift 260188
  have htrace : WordTrace (prefixWord ++ tailWord_260188) baseStart_260188 baseEnd_260188 := by
    simpa [prefixWord, tailWord_260188, baseEnd_260188] using wordTrace_append hprefix tailTrace_260188
  have hstable : (prefixWord ++ tailWord_260188).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260188).length < 2 ^ (prefixWord ++ tailWord_260188).sum := by decide
  have hdescent : baseEnd_260188 < baseStart_260188 := by decide
  rcases family_descends (prefixWord ++ tailWord_260188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260247 : List Nat := [1, 1, 3, 3, 4, 1, 1, 5]
def baseStart_260247 : Nat := 118140960795 + 260247 * 2 ^ 59
def prefixEnd_260247 : Nat := 4983230072969 + 3 ^ 40 * 260247 * 2
def baseEnd_260247 : Nat := 79189214750073194735201

theorem tailTrace_260247 : CollatzResearch.WordTrace tailWord_260247 prefixEnd_260247 79189214750073194735201 := by
  unfold tailWord_260247
  simp only [CollatzResearch.WordTrace]
  refine ⟨9491987888177040494130995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6327991925451360329420663 9491987888177040494130995)
  ·
    refine ⟨14237981832265560741196493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9491987888177040494130995 14237981832265560741196493)
    ·
      refine ⟨5339243187099585277948685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14237981832265560741196493 5339243187099585277948685)
      ·
        refine ⟨2002216195162344479230757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5339243187099585277948685 2002216195162344479230757)
        ·
          refine ⟨375415536592939589855767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2002216195162344479230757 375415536592939589855767)
          ·
            refine ⟨563123304889409384783651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375415536592939589855767 563123304889409384783651)
            ·
              refine ⟨844684957334114077175477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563123304889409384783651 844684957334114077175477)
              ·
                refine ⟨79189214750073194735201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 844684957334114077175477 79189214750073194735201)
                ·
                  rfl

theorem cell19_260247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 5].length) (baseStart_260247 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260247 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260247 prefixEnd_260247 := by exact prefixLift 260247
  have htrace : WordTrace (prefixWord ++ tailWord_260247) baseStart_260247 baseEnd_260247 := by
    simpa [prefixWord, tailWord_260247, baseEnd_260247] using wordTrace_append hprefix tailTrace_260247
  have hstable : (prefixWord ++ tailWord_260247).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260247).length < 2 ^ (prefixWord ++ tailWord_260247).sum := by decide
  have hdescent : baseEnd_260247 < baseStart_260247 := by decide
  rcases family_descends (prefixWord ++ tailWord_260247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260323 : List Nat := [1, 1, 1, 8, 1, 7]
def baseStart_260323 : Nat := 118140960795 + 260323 * 2 ^ 59
def prefixEnd_260323 : Nat := 4983230072969 + 3 ^ 40 * 260323 * 2
def baseEnd_260323 : Nat := 8801371155258615227345

theorem tailTrace_260323 : CollatzResearch.WordTrace tailWord_260323 prefixEnd_260323 8801371155258615227345 := by
  unfold tailWord_260323
  simp only [CollatzResearch.WordTrace]
  refine ⟨9494759835901705473897623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6329839890601136982598415 9494759835901705473897623)
  ·
    refine ⟨14242139753852558210846435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9494759835901705473897623 14242139753852558210846435)
    ·
      refine ⟨21363209630778837316269653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14242139753852558210846435 21363209630778837316269653)
      ·
        refine ⟨250350112860689499800035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 21363209630778837316269653 250350112860689499800035)
        ·
          refine ⟨375525169291034249700053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250350112860689499800035 375525169291034249700053)
          ·
            refine ⟨8801371155258615227345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 375525169291034249700053 8801371155258615227345)
            ·
              rfl

theorem cell19_260323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 7].length) (baseStart_260323 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260323 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260323 prefixEnd_260323 := by exact prefixLift 260323
  have htrace : WordTrace (prefixWord ++ tailWord_260323) baseStart_260323 baseEnd_260323 := by
    simpa [prefixWord, tailWord_260323, baseEnd_260323] using wordTrace_append hprefix tailTrace_260323
  have hstable : (prefixWord ++ tailWord_260323).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260323).length < 2 ^ (prefixWord ++ tailWord_260323).sum := by decide
  have hdescent : baseEnd_260323 < baseStart_260323 := by decide
  rcases family_descends (prefixWord ++ tailWord_260323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260325 : List Nat := [1, 3, 1, 4, 2, 8]
def baseStart_260325 : Nat := 118140960795 + 260325 * 2 ^ 59
def prefixEnd_260325 : Nat := 4983230072969 + 3 ^ 40 * 260325 * 2
def baseEnd_260325 : Nat := 8801438774110236111295

theorem tailTrace_260325 : CollatzResearch.WordTrace tailWord_260325 prefixEnd_260325 8801438774110236111295 := by
  unfold tailWord_260325
  simp only [CollatzResearch.WordTrace]
  refine ⟨9494832781894459815470429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6329888521262973210313619 9494832781894459815470429)
  ·
    refine ⟨3560562293210422430801411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9494832781894459815470429 3560562293210422430801411)
    ·
      refine ⟨5340843439815633646202117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3560562293210422430801411 5340843439815633646202117)
      ·
        refine ⟨1001408144965431308662897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5340843439815633646202117 1001408144965431308662897)
        ·
          refine ⟨751056108724073481497173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1001408144965431308662897 751056108724073481497173)
          ·
            refine ⟨8801438774110236111295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 751056108724073481497173 8801438774110236111295)
            ·
              rfl

theorem cell19_260325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 8].length) (baseStart_260325 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260325 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260325 prefixEnd_260325 := by exact prefixLift 260325
  have htrace : WordTrace (prefixWord ++ tailWord_260325) baseStart_260325 baseEnd_260325 := by
    simpa [prefixWord, tailWord_260325, baseEnd_260325] using wordTrace_append hprefix tailTrace_260325
  have hstable : (prefixWord ++ tailWord_260325).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260325).length < 2 ^ (prefixWord ++ tailWord_260325).sum := by decide
  have hdescent : baseEnd_260325 < baseStart_260325 := by decide
  rcases family_descends (prefixWord ++ tailWord_260325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260342 : List Nat := [5, 1, 1, 1, 1, 1, 5, 4]
def baseStart_260342 : Nat := 118140960795 + 260342 * 2 ^ 59
def prefixEnd_260342 : Nat := 4983230072969 + 3 ^ 40 * 260342 * 2
def baseEnd_260342 : Nat := 79218121809141122623831

theorem tailTrace_260342 : CollatzResearch.WordTrace tailWord_260342 prefixEnd_260342 79218121809141122623831 := by
  unfold tailWord_260342
  simp only [CollatzResearch.WordTrace]
  refine ⟨593465801427054482427455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6330301881888581145892853 593465801427054482427455)
  ·
    refine ⟨890198702140581723641183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 593465801427054482427455 890198702140581723641183)
    ·
      refine ⟨1335298053210872585461775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 890198702140581723641183 1335298053210872585461775)
      ·
        refine ⟨2002947079816308878192663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335298053210872585461775 2002947079816308878192663)
        ·
          refine ⟨3004420619724463317288995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002947079816308878192663 3004420619724463317288995)
          ·
            refine ⟨4506630929586694975933493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3004420619724463317288995 4506630929586694975933493)
            ·
              refine ⟨422496649648752653993765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4506630929586694975933493 422496649648752653993765)
              ·
                refine ⟨79218121809141122623831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422496649648752653993765 79218121809141122623831)
                ·
                  rfl

theorem cell19_260342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_260342 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260342 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260342 prefixEnd_260342 := by exact prefixLift 260342
  have htrace : WordTrace (prefixWord ++ tailWord_260342) baseStart_260342 baseEnd_260342 := by
    simpa [prefixWord, tailWord_260342, baseEnd_260342] using wordTrace_append hprefix tailTrace_260342
  have hstable : (prefixWord ++ tailWord_260342).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260342).length < 2 ^ (prefixWord ++ tailWord_260342).sum := by decide
  have hdescent : baseEnd_260342 < baseStart_260342 := by decide
  rcases family_descends (prefixWord ++ tailWord_260342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260361 : List Nat := [1, 2, 1, 1, 3, 5, 3, 3]
def baseStart_260361 : Nat := 118140960795 + 260361 * 2 ^ 59
def prefixEnd_260361 : Nat := 4983230072969 + 3 ^ 40 * 260361 * 2
def baseEnd_260361 : Nat := 79223903220954708201557

theorem tailTrace_260361 : CollatzResearch.WordTrace tailWord_260361 prefixEnd_260361 79223903220954708201557 := by
  unfold tailWord_260361
  simp only [CollatzResearch.WordTrace]
  refine ⟨9496145809764037963780937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6330763873176025309187291 9496145809764037963780937)
  ·
    refine ⟨7122109357323028472835703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9496145809764037963780937 7122109357323028472835703)
    ·
      refine ⟨10683164035984542709253555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7122109357323028472835703 10683164035984542709253555)
      ·
        refine ⟨16024746053976814063880333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10683164035984542709253555 16024746053976814063880333)
        ·
          refine ⟨6009279770241305273955125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16024746053976814063880333 6009279770241305273955125)
          ·
            refine ⟨563369978460122369433293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6009279770241305273955125 563369978460122369433293)
            ·
              refine ⟨211263741922545888537485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 563369978460122369433293 211263741922545888537485)
              ·
                refine ⟨79223903220954708201557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211263741922545888537485 79223903220954708201557)
                ·
                  rfl

theorem cell19_260361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 3].length) (baseStart_260361 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260361 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260361 prefixEnd_260361 := by exact prefixLift 260361
  have htrace : WordTrace (prefixWord ++ tailWord_260361) baseStart_260361 baseEnd_260361 := by
    simpa [prefixWord, tailWord_260361, baseEnd_260361] using wordTrace_append hprefix tailTrace_260361
  have hstable : (prefixWord ++ tailWord_260361).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260361).length < 2 ^ (prefixWord ++ tailWord_260361).sum := by decide
  have hdescent : baseEnd_260361 < baseStart_260361 := by decide
  rcases family_descends (prefixWord ++ tailWord_260361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260437 : List Nat := [1, 3, 2, 2, 4, 2, 5]
def baseStart_260437 : Nat := 118140960795 + 260437 * 2 ^ 59
def prefixEnd_260437 : Nat := 4983230072969 + 3 ^ 40 * 260437 * 2
def baseEnd_260437 : Nat := 26415676289403016837487

theorem tailTrace_260437 : CollatzResearch.WordTrace tailWord_260437 prefixEnd_260437 26415676289403016837487 := by
  unfold tailWord_260437
  simp only [CollatzResearch.WordTrace]
  refine ⟨9498917757488702943547565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6332611838325801962365043 9498917757488702943547565)
  ·
    refine ⟨3562094159058263603830337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9498917757488702943547565 3562094159058263603830337)
    ·
      refine ⟨2671570619293697702872753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3562094159058263603830337 2671570619293697702872753)
      ·
        refine ⟨2003677964470273277154565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2671570619293697702872753 2003677964470273277154565)
        ·
          refine ⟨375689618338176239466481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2003677964470273277154565 375689618338176239466481)
          ·
            refine ⟨281767213753632179599861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375689618338176239466481 281767213753632179599861)
            ·
              refine ⟨26415676289403016837487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 281767213753632179599861 26415676289403016837487)
              ·
                rfl

theorem cell19_260437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 5].length) (baseStart_260437 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260437 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260437 prefixEnd_260437 := by exact prefixLift 260437
  have htrace : WordTrace (prefixWord ++ tailWord_260437) baseStart_260437 baseEnd_260437 := by
    simpa [prefixWord, tailWord_260437, baseEnd_260437] using wordTrace_append hprefix tailTrace_260437
  have hstable : (prefixWord ++ tailWord_260437).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260437).length < 2 ^ (prefixWord ++ tailWord_260437).sum := by decide
  have hdescent : baseEnd_260437 < baseStart_260437 := by decide
  rcases family_descends (prefixWord ++ tailWord_260437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260456 : List Nat := [2, 1, 4, 2, 2, 2, 2, 4]
def baseStart_260456 : Nat := 118140960795 + 260456 * 2 ^ 59
def prefixEnd_260456 : Nat := 4983230072969 + 3 ^ 40 * 260456 * 2
def baseEnd_260456 : Nat := 79252810280022636090187

theorem tailTrace_260456 : CollatzResearch.WordTrace tailWord_260456 prefixEnd_260456 79252810280022636090187 := by
  unfold tailWord_260456
  simp only [CollatzResearch.WordTrace]
  refine ⟨4749805372209934594244611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6333073829613246125659481 4749805372209934594244611)
  ·
    refine ⟨7124708058314901891366917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4749805372209934594244611 7124708058314901891366917)
    ·
      refine ⟨1335882760934044104631297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7124708058314901891366917 1335882760934044104631297)
      ·
        refine ⟨1001912070700533078473473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1335882760934044104631297 1001912070700533078473473)
        ·
          refine ⟨751434053025399808855105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1001912070700533078473473 751434053025399808855105)
          ·
            refine ⟨563575539769049856641329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 751434053025399808855105 563575539769049856641329)
            ·
              refine ⟨422681654826787392480997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563575539769049856641329 422681654826787392480997)
              ·
                refine ⟨79252810280022636090187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422681654826787392480997 79252810280022636090187)
                ·
                  rfl

theorem cell19_260456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_260456 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260456 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260456 prefixEnd_260456 := by exact prefixLift 260456
  have htrace : WordTrace (prefixWord ++ tailWord_260456) baseStart_260456 baseEnd_260456 := by
    simpa [prefixWord, tailWord_260456, baseEnd_260456] using wordTrace_append hprefix tailTrace_260456
  have hstable : (prefixWord ++ tailWord_260456).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260456).length < 2 ^ (prefixWord ++ tailWord_260456).sum := by decide
  have hdescent : baseEnd_260456 < baseStart_260456 := by decide
  rcases family_descends (prefixWord ++ tailWord_260456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260477 : List Nat := [1, 4, 1, 1, 2, 3, 2, 5]
def baseStart_260477 : Nat := 118140960795 + 260477 * 2 ^ 59
def prefixEnd_260477 : Nat := 4983230072969 + 3 ^ 40 * 260477 * 2
def baseEnd_260477 : Nat := 79259200261500809623463

theorem tailTrace_260477 : CollatzResearch.WordTrace tailWord_260477 prefixEnd_260477 79259200261500809623463 := by
  unfold tailWord_260477
  simp only [CollatzResearch.WordTrace]
  refine ⟨9500376677343789775003685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6333584451562526516669123 9500376677343789775003685)
  ·
    refine ⟨1781320627001960582813191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9500376677343789775003685 1781320627001960582813191)
    ·
      refine ⟨2671980940502940874219787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1781320627001960582813191 2671980940502940874219787)
      ·
        refine ⟨4007971410754411311329681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2671980940502940874219787 4007971410754411311329681)
        ·
          refine ⟨3005978558065808483497261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4007971410754411311329681 3005978558065808483497261)
          ·
            refine ⟨1127241959274678181311473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3005978558065808483497261 1127241959274678181311473)
            ·
              refine ⟨845431469456008635983605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1127241959274678181311473 845431469456008635983605)
              ·
                refine ⟨79259200261500809623463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 845431469456008635983605 79259200261500809623463)
                ·
                  rfl

theorem cell19_260477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_260477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260477 prefixEnd_260477 := by exact prefixLift 260477
  have htrace : WordTrace (prefixWord ++ tailWord_260477) baseStart_260477 baseEnd_260477 := by
    simpa [prefixWord, tailWord_260477, baseEnd_260477] using wordTrace_append hprefix tailTrace_260477
  have hstable : (prefixWord ++ tailWord_260477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260477).length < 2 ^ (prefixWord ++ tailWord_260477).sum := by decide
  have hdescent : baseEnd_260477 < baseStart_260477 := by decide
  rcases family_descends (prefixWord ++ tailWord_260477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260515 : List Nat := [1, 1, 1, 4, 1, 4, 3, 4]
def baseStart_260515 : Nat := 118140960795 + 260515 * 2 ^ 59
def prefixEnd_260515 : Nat := 4983230072969 + 3 ^ 40 * 260515 * 2
def baseEnd_260515 : Nat := 79270763085127980778915

theorem tailTrace_260515 : CollatzResearch.WordTrace tailWord_260515 prefixEnd_260515 79270763085127980778915 := by
  unfold tailWord_260515
  simp only [CollatzResearch.WordTrace]
  refine ⟨9501762651206122264886999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6334508434137414843257999 9501762651206122264886999)
  ·
    refine ⟨14252643976809183397330499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9501762651206122264886999 14252643976809183397330499)
    ·
      refine ⟨21378965965213775095995749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14252643976809183397330499 21378965965213775095995749)
      ·
        refine ⟨4008556118477582830499203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21378965965213775095995749 4008556118477582830499203)
        ·
          refine ⟨6012834177716374245748805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4008556118477582830499203 6012834177716374245748805)
          ·
            refine ⟨1127406408321820171077901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6012834177716374245748805 1127406408321820171077901)
            ·
              refine ⟨422777403120682564154213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1127406408321820171077901 422777403120682564154213)
              ·
                refine ⟨79270763085127980778915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422777403120682564154213 79270763085127980778915)
                ·
                  rfl

theorem cell19_260515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_260515 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260515 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260515 prefixEnd_260515 := by exact prefixLift 260515
  have htrace : WordTrace (prefixWord ++ tailWord_260515) baseStart_260515 baseEnd_260515 := by
    simpa [prefixWord, tailWord_260515, baseEnd_260515] using wordTrace_append hprefix tailTrace_260515
  have hstable : (prefixWord ++ tailWord_260515).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260515).length < 2 ^ (prefixWord ++ tailWord_260515).sum := by decide
  have hdescent : baseEnd_260515 < baseStart_260515 := by decide
  rcases family_descends (prefixWord ++ tailWord_260515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260589 : List Nat := [1, 5, 1, 3, 1, 2, 1, 5]
def baseStart_260589 : Nat := 118140960795 + 260589 * 2 ^ 59
def prefixEnd_260589 : Nat := 4983230072969 + 3 ^ 40 * 260589 * 2
def baseEnd_260589 : Nat := 79293280162717735134269

theorem tailTrace_260589 : CollatzResearch.WordTrace tailWord_260589 prefixEnd_260589 79293280162717735134269 := by
  unfold tailWord_260589
  simp only [CollatzResearch.WordTrace]
  refine ⟨9504461652938032903080821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6336307768625355268720547 9504461652938032903080821)
  ·
    refine ⟨891043279962940584663827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9504461652938032903080821 891043279962940584663827)
    ·
      refine ⟨1336564919944410876995741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 891043279962940584663827 1336564919944410876995741)
      ·
        refine ⟨501211844979154078873403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1336564919944410876995741 501211844979154078873403)
        ·
          refine ⟨751817767468731118310105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501211844979154078873403 751817767468731118310105)
          ·
            refine ⟨563863325601548338732579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 751817767468731118310105 563863325601548338732579)
            ·
              refine ⟨845794988402322508098869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563863325601548338732579 845794988402322508098869)
              ·
                refine ⟨79293280162717735134269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 845794988402322508098869 79293280162717735134269)
                ·
                  rfl

theorem cell19_260589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_260589 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260589 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260589 prefixEnd_260589 := by exact prefixLift 260589
  have htrace : WordTrace (prefixWord ++ tailWord_260589) baseStart_260589 baseEnd_260589 := by
    simpa [prefixWord, tailWord_260589, baseEnd_260589] using wordTrace_append hprefix tailTrace_260589
  have hstable : (prefixWord ++ tailWord_260589).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260589).length < 2 ^ (prefixWord ++ tailWord_260589).sum := by decide
  have hdescent : baseEnd_260589 < baseStart_260589 := by decide
  rcases family_descends (prefixWord ++ tailWord_260589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260629 : List Nat := [1, 3, 2, 1, 3, 1, 4, 4]
def baseStart_260629 : Nat := 118140960795 + 260629 * 2 ^ 59
def prefixEnd_260629 : Nat := 4983230072969 + 3 ^ 40 * 260629 * 2
def baseEnd_260629 : Nat := 79305451556009494245271

theorem tailTrace_260629 : CollatzResearch.WordTrace tailWord_260629 prefixEnd_260629 79305451556009494245271 := by
  unfold tailWord_260629
  simp only [CollatzResearch.WordTrace]
  refine ⟨9505920572793119734536941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6337280381862079823024627 9505920572793119734536941)
  ·
    refine ⟨3564720214797419900451353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9505920572793119734536941 3564720214797419900451353)
    ·
      refine ⟨2673540161098064925338515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3564720214797419900451353 2673540161098064925338515)
      ·
        refine ⟨4010310241647097388007773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2673540161098064925338515 4010310241647097388007773)
        ·
          refine ⟨1503866340617661520502915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4010310241647097388007773 1503866340617661520502915)
          ·
            refine ⟨2255799510926492280754373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503866340617661520502915 2255799510926492280754373)
            ·
              refine ⟨422962408298717302641445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2255799510926492280754373 422962408298717302641445)
              ·
                refine ⟨79305451556009494245271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422962408298717302641445 79305451556009494245271)
                ·
                  rfl

theorem cell19_260629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_260629 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260629 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260629 prefixEnd_260629 := by exact prefixLift 260629
  have htrace : WordTrace (prefixWord ++ tailWord_260629) baseStart_260629 baseEnd_260629 := by
    simpa [prefixWord, tailWord_260629, baseEnd_260629] using wordTrace_append hprefix tailTrace_260629
  have hstable : (prefixWord ++ tailWord_260629).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260629).length < 2 ^ (prefixWord ++ tailWord_260629).sum := by decide
  have hdescent : baseEnd_260629 < baseStart_260629 := by decide
  rcases family_descends (prefixWord ++ tailWord_260629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260686 : List Nat := [4, 1, 1, 1, 1, 2, 5, 4]
def baseStart_260686 : Nat := 118140960795 + 260686 * 2 ^ 59
def prefixEnd_260686 : Nat := 4983230072969 + 3 ^ 40 * 260686 * 2
def baseEnd_260686 : Nat := 79322795791450250978449

theorem tailTrace_260686 : CollatzResearch.WordTrace tailWord_260686 prefixEnd_260686 79322795791450250978449 := by
  unfold tailWord_260686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1188499941698327308670239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6338666355724412312907941 1188499941698327308670239)
  ·
    refine ⟨1782749912547490963005359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1188499941698327308670239 1782749912547490963005359)
    ·
      refine ⟨2674124868821236444508039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1782749912547490963005359 2674124868821236444508039)
      ·
        refine ⟨4011187303231854666762059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2674124868821236444508039 4011187303231854666762059)
        ·
          refine ⟨6016780954847782000143089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4011187303231854666762059 6016780954847782000143089)
          ·
            refine ⟨4512585716135836500107317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6016780954847782000143089 4512585716135836500107317)
            ·
              refine ⟨423054910887734671885061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4512585716135836500107317 423054910887734671885061)
              ·
                refine ⟨79322795791450250978449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423054910887734671885061 79322795791450250978449)
                ·
                  rfl

theorem cell19_260686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_260686 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260686 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260686 prefixEnd_260686 := by exact prefixLift 260686
  have htrace : WordTrace (prefixWord ++ tailWord_260686) baseStart_260686 baseEnd_260686 := by
    simpa [prefixWord, tailWord_260686, baseEnd_260686] using wordTrace_append hprefix tailTrace_260686
  have hstable : (prefixWord ++ tailWord_260686).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260686).length < 2 ^ (prefixWord ++ tailWord_260686).sum := by decide
  have hdescent : baseEnd_260686 < baseStart_260686 := by decide
  rcases family_descends (prefixWord ++ tailWord_260686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260688 : List Nat := [2, 1, 1, 1, 1, 3, 2, 8]
def baseStart_260688 : Nat := 118140960795 + 260688 * 2 ^ 59
def prefixEnd_260688 : Nat := 4983230072969 + 3 ^ 40 * 260688 * 2
def baseEnd_260688 : Nat := 79323404361114838933999

theorem tailTrace_260688 : CollatzResearch.WordTrace tailWord_260688 prefixEnd_260688 79323404361114838933999 := by
  unfold tailWord_260688
  simp only [CollatzResearch.WordTrace]
  refine ⟨4754036239789686405467359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6338714986386248540623145 4754036239789686405467359)
  ·
    refine ⟨7131054359684529608201039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4754036239789686405467359 7131054359684529608201039)
    ·
      refine ⟨10696581539526794412301559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7131054359684529608201039 10696581539526794412301559)
      ·
        refine ⟨16044872309290191618452339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10696581539526794412301559 16044872309290191618452339)
        ·
          refine ⟨24067308463935287427678509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16044872309290191618452339 24067308463935287427678509)
          ·
            refine ⟨9025240673975732785379441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24067308463935287427678509 9025240673975732785379441)
            ·
              refine ⟨6768930505481799589034581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9025240673975732785379441 6768930505481799589034581)
              ·
                refine ⟨79323404361114838933999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6768930505481799589034581 79323404361114838933999)
                ·
                  rfl

theorem cell19_260688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_260688 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260688 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260688 prefixEnd_260688 := by exact prefixLift 260688
  have htrace : WordTrace (prefixWord ++ tailWord_260688) baseStart_260688 baseEnd_260688 := by
    simpa [prefixWord, tailWord_260688, baseEnd_260688] using wordTrace_append hprefix tailTrace_260688
  have hstable : (prefixWord ++ tailWord_260688).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260688).length < 2 ^ (prefixWord ++ tailWord_260688).sum := by decide
  have hdescent : baseEnd_260688 < baseStart_260688 := by decide
  rcases family_descends (prefixWord ++ tailWord_260688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260745 : List Nat := [1, 2, 1, 1, 4, 1, 1, 8]
def baseStart_260745 : Nat := 118140960795 + 260745 * 2 ^ 59
def prefixEnd_260745 : Nat := 4983230072969 + 3 ^ 40 * 260745 * 2
def baseEnd_260745 : Nat := 79340748596555595667177

theorem tailTrace_260745 : CollatzResearch.WordTrace tailWord_260745 prefixEnd_260745 79340748596555595667177 := by
  unfold tailWord_260745
  simp only [CollatzResearch.WordTrace]
  refine ⟨9510151440372871545759689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6340100960248581030506459 9510151440372871545759689)
  ·
    refine ⟨7132613580279653659319767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9510151440372871545759689 7132613580279653659319767)
    ·
      refine ⟨10698920370419480488979651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7132613580279653659319767 10698920370419480488979651)
      ·
        refine ⟨16048380555629220733469477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10698920370419480488979651 16048380555629220733469477)
        ·
          refine ⟨3009071354180478887525527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16048380555629220733469477 3009071354180478887525527)
          ·
            refine ⟨4513607031270718331288291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3009071354180478887525527 4513607031270718331288291)
            ·
              refine ⟨6770410546906077496932437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4513607031270718331288291 6770410546906077496932437)
              ·
                refine ⟨79340748596555595667177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6770410546906077496932437 79340748596555595667177)
                ·
                  rfl

theorem cell19_260745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_260745 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260745 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260745 prefixEnd_260745 := by exact prefixLift 260745
  have htrace : WordTrace (prefixWord ++ tailWord_260745) baseStart_260745 baseEnd_260745 := by
    simpa [prefixWord, tailWord_260745, baseEnd_260745] using wordTrace_append hprefix tailTrace_260745
  have hstable : (prefixWord ++ tailWord_260745).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260745).length < 2 ^ (prefixWord ++ tailWord_260745).sum := by decide
  have hdescent : baseEnd_260745 < baseStart_260745 := by decide
  rcases family_descends (prefixWord ++ tailWord_260745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260781 : List Nat := [1, 5, 2, 1, 1, 2, 7]
def baseStart_260781 : Nat := 118140960795 + 260781 * 2 ^ 59
def prefixEnd_260781 : Nat := 4983230072969 + 3 ^ 40 * 260781 * 2
def baseEnd_260781 : Nat := 26450567616839392955693

theorem tailTrace_260781 : CollatzResearch.WordTrace tailWord_260781 prefixEnd_260781 26450567616839392955693 := by
  unfold tailWord_260781
  simp only [CollatzResearch.WordTrace]
  refine ⟨9511464468242449694070197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6340976312161633129380131 9511464468242449694070197)
  ·
    refine ⟨891699793897729658819081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9511464468242449694070197 891699793897729658819081)
    ·
      refine ⟨668774845423297244114311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 891699793897729658819081 668774845423297244114311)
      ·
        refine ⟨1003162268134945866171467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668774845423297244114311 1003162268134945866171467)
        ·
          refine ⟨1504743402202418799257201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003162268134945866171467 1504743402202418799257201)
          ·
            refine ⟨1128557551651814099442901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1504743402202418799257201 1128557551651814099442901)
            ·
              refine ⟨26450567616839392955693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1128557551651814099442901 26450567616839392955693)
              ·
                rfl

theorem cell19_260781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 7].length) (baseStart_260781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260781 prefixEnd_260781 := by exact prefixLift 260781
  have htrace : WordTrace (prefixWord ++ tailWord_260781) baseStart_260781 baseEnd_260781 := by
    simpa [prefixWord, tailWord_260781, baseEnd_260781] using wordTrace_append hprefix tailTrace_260781
  have hstable : (prefixWord ++ tailWord_260781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260781).length < 2 ^ (prefixWord ++ tailWord_260781).sum := by decide
  have hdescent : baseEnd_260781 < baseStart_260781 := by decide
  rcases family_descends (prefixWord ++ tailWord_260781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260783 : List Nat := [1, 1, 2, 1, 2, 5, 7]
def baseStart_260783 : Nat := 118140960795 + 260783 * 2 ^ 59
def prefixEnd_260783 : Nat := 4983230072969 + 3 ^ 40 * 260783 * 2
def baseEnd_260783 : Nat := 26450770473394255607543

theorem tailTrace_260783 : CollatzResearch.WordTrace tailWord_260783 prefixEnd_260783 26450770473394255607543 := by
  unfold tailWord_260783
  simp only [CollatzResearch.WordTrace]
  refine ⟨9511537414235204035643003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6341024942823469357095335 9511537414235204035643003)
  ·
    refine ⟨14267306121352806053464505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9511537414235204035643003 14267306121352806053464505)
    ·
      refine ⟨10700479591014604540098379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14267306121352806053464505 10700479591014604540098379)
      ·
        refine ⟨16050719386521906810147569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10700479591014604540098379 16050719386521906810147569)
        ·
          refine ⟨12038039539891430107610677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16050719386521906810147569 12038039539891430107610677)
          ·
            refine ⟨1128566206864821572588501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12038039539891430107610677 1128566206864821572588501)
            ·
              refine ⟨26450770473394255607543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1128566206864821572588501 26450770473394255607543)
              ·
                rfl

theorem cell19_260783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 7].length) (baseStart_260783 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260783 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260783 prefixEnd_260783 := by exact prefixLift 260783
  have htrace : WordTrace (prefixWord ++ tailWord_260783) baseStart_260783 baseEnd_260783 := by
    simpa [prefixWord, tailWord_260783, baseEnd_260783] using wordTrace_append hprefix tailTrace_260783
  have hstable : (prefixWord ++ tailWord_260783).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260783).length < 2 ^ (prefixWord ++ tailWord_260783).sum := by decide
  have hdescent : baseEnd_260783 < baseStart_260783 := by decide
  rcases family_descends (prefixWord ++ tailWord_260783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260800 : List Nat := [2, 1, 1, 2, 4, 3, 2, 4]
def baseStart_260800 : Nat := 118140960795 + 260800 * 2 ^ 59
def prefixEnd_260800 : Nat := 4983230072969 + 3 ^ 40 * 260800 * 2
def baseEnd_260800 : Nat := 79357484262331764444805

theorem tailTrace_260800 : CollatzResearch.WordTrace tailWord_260800 prefixEnd_260800 79357484262331764444805 := by
  unfold tailWord_260800
  simp only [CollatzResearch.WordTrace]
  refine ⟨4756078727586807969505927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6341438303449077292674569 4756078727586807969505927)
  ·
    refine ⟨7134118091380211954258891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4756078727586807969505927 7134118091380211954258891)
    ·
      refine ⟨10701177137070317931388337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7134118091380211954258891 10701177137070317931388337)
      ·
        refine ⟨8025882852802738448541253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10701177137070317931388337 8025882852802738448541253)
        ·
          refine ⟨1504853034900513459101485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8025882852802738448541253 1504853034900513459101485)
          ·
            refine ⟨564319888087692547163057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1504853034900513459101485 564319888087692547163057)
            ·
              refine ⟨423239916065769410372293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564319888087692547163057 423239916065769410372293)
              ·
                refine ⟨79357484262331764444805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423239916065769410372293 79357484262331764444805)
                ·
                  rfl

theorem cell19_260800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_260800 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260800 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260800 prefixEnd_260800 := by exact prefixLift 260800
  have htrace : WordTrace (prefixWord ++ tailWord_260800) baseStart_260800 baseEnd_260800 := by
    simpa [prefixWord, tailWord_260800, baseEnd_260800] using wordTrace_append hprefix tailTrace_260800
  have hstable : (prefixWord ++ tailWord_260800).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260800).length < 2 ^ (prefixWord ++ tailWord_260800).sum := by decide
  have hdescent : baseEnd_260800 < baseStart_260800 := by decide
  rcases family_descends (prefixWord ++ tailWord_260800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260840 : List Nat := [2, 1, 4, 1, 11]
def baseStart_260840 : Nat := 118140960795 + 260840 * 2 ^ 59
def prefixEnd_260840 : Nat := 4983230072969 + 3 ^ 40 * 260840 * 2
def baseEnd_260840 : Nat := 2939616876134204576141

theorem tailTrace_260840 : CollatzResearch.WordTrace tailWord_260840 prefixEnd_260840 2939616876134204576141 := by
  unfold tailWord_260840
  simp only [CollatzResearch.WordTrace]
  refine ⟨4756808187514351385233987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6342410916685801846978649 4756808187514351385233987)
  ·
    refine ⟨7135212281271527077850981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4756808187514351385233987 7135212281271527077850981)
    ·
      refine ⟨1337852302738411327097059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7135212281271527077850981 1337852302738411327097059)
      ·
        refine ⟨2006778454107616990645589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1337852302738411327097059 2006778454107616990645589)
        ·
          refine ⟨2939616876134204576141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2006778454107616990645589 2939616876134204576141)
          ·
            rfl

theorem cell19_260840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 11].length) (baseStart_260840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260840 prefixEnd_260840 := by exact prefixLift 260840
  have htrace : WordTrace (prefixWord ++ tailWord_260840) baseStart_260840 baseEnd_260840 := by
    simpa [prefixWord, tailWord_260840, baseEnd_260840] using wordTrace_append hprefix tailTrace_260840
  have hstable : (prefixWord ++ tailWord_260840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260840).length < 2 ^ (prefixWord ++ tailWord_260840).sum := by decide
  have hdescent : baseEnd_260840 < baseStart_260840 := by decide
  rcases family_descends (prefixWord ++ tailWord_260840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260893 : List Nat := [1, 4, 2, 4, 1, 1, 6]
def baseStart_260893 : Nat := 118140960795 + 260893 * 2 ^ 59
def prefixEnd_260893 : Nat := 4983230072969 + 3 ^ 40 * 260893 * 2
def baseEnd_260893 : Nat := 26461927583911701459295

theorem tailTrace_260893 : CollatzResearch.WordTrace tailWord_260893 prefixEnd_260893 26461927583911701459295 := by
  unfold tailWord_260893
  simp only [CollatzResearch.WordTrace]
  refine ⟨9515549443836692822147333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6343699629224461881431555 9515549443836692822147333)
  ·
    refine ⟨1784165520719379904152625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9515549443836692822147333 1784165520719379904152625)
    ·
      refine ⟨1338124140539534928114469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1784165520719379904152625 1338124140539534928114469)
      ·
        refine ⟨250898276351162799021463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1338124140539534928114469 250898276351162799021463)
        ·
          refine ⟨376347414526744198532195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250898276351162799021463 376347414526744198532195)
          ·
            refine ⟨564521121790116297798293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376347414526744198532195 564521121790116297798293)
            ·
              refine ⟨26461927583911701459295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 564521121790116297798293 26461927583911701459295)
              ·
                rfl

theorem cell19_260893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 6].length) (baseStart_260893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260893 prefixEnd_260893 := by exact prefixLift 260893
  have htrace : WordTrace (prefixWord ++ tailWord_260893) baseStart_260893 baseEnd_260893 := by
    simpa [prefixWord, tailWord_260893, baseEnd_260893] using wordTrace_append hprefix tailTrace_260893
  have hstable : (prefixWord ++ tailWord_260893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260893).length < 2 ^ (prefixWord ++ tailWord_260893).sum := by decide
  have hdescent : baseEnd_260893 < baseStart_260893 := by decide
  rcases family_descends (prefixWord ++ tailWord_260893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260897 : List Nat := [1, 2, 3, 2, 1, 2, 8]
def baseStart_260897 : Nat := 118140960795 + 260897 * 2 ^ 59
def prefixEnd_260897 : Nat := 4983230072969 + 3 ^ 40 * 260897 * 2
def baseEnd_260897 : Nat := 26462333297021426762995

theorem tailTrace_260897 : CollatzResearch.WordTrace tailWord_260897 prefixEnd_260897 26462333297021426762995 := by
  unfold tailWord_260897
  simp only [CollatzResearch.WordTrace]
  refine ⟨9515695335822201505292945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6343796890548134336861963 9515695335822201505292945)
  ·
    refine ⟨7136771501866651128969709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9515695335822201505292945 7136771501866651128969709)
    ·
      refine ⟨2676289313199994173363641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7136771501866651128969709 2676289313199994173363641)
      ·
        refine ⟨2007216984899995630022731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2676289313199994173363641 2007216984899995630022731)
        ·
          refine ⟨3010825477349993445034097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2007216984899995630022731 3010825477349993445034097)
          ·
            refine ⟨2258119108012495083775573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3010825477349993445034097 2258119108012495083775573)
            ·
              refine ⟨26462333297021426762995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2258119108012495083775573 26462333297021426762995)
              ·
                rfl

theorem cell19_260897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 8].length) (baseStart_260897 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260897 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260897 prefixEnd_260897 := by exact prefixLift 260897
  have htrace : WordTrace (prefixWord ++ tailWord_260897) baseStart_260897 baseEnd_260897 := by
    simpa [prefixWord, tailWord_260897, baseEnd_260897] using wordTrace_append hprefix tailTrace_260897
  have hstable : (prefixWord ++ tailWord_260897).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260897).length < 2 ^ (prefixWord ++ tailWord_260897).sum := by decide
  have hdescent : baseEnd_260897 < baseStart_260897 := by decide
  rcases family_descends (prefixWord ++ tailWord_260897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260954 : List Nat := [3, 1, 1, 2, 1, 4, 7]
def baseStart_260954 : Nat := 118140960795 + 260954 * 2 ^ 59
def prefixEnd_260954 : Nat := 4983230072969 + 3 ^ 40 * 260954 * 2
def baseEnd_260954 : Nat := 26468114708835012340721

theorem tailTrace_260954 : CollatzResearch.WordTrace tailWord_260954 prefixEnd_260954 26468114708835012340721 := by
  unfold tailWord_260954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2379443574153925060029479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6345182864410466826745277 2379443574153925060029479)
  ·
    refine ⟨3569165361230887590044219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2379443574153925060029479 3569165361230887590044219)
    ·
      refine ⟨5353748041846331385066329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3569165361230887590044219 5353748041846331385066329)
      ·
        refine ⟨4015311031384748538799747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5353748041846331385066329 4015311031384748538799747)
        ·
          refine ⟨6022966547077122808199621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4015311031384748538799747 6022966547077122808199621)
          ·
            refine ⟨1129306227576960526537429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6022966547077122808199621 1129306227576960526537429)
            ·
              refine ⟨26468114708835012340721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1129306227576960526537429 26468114708835012340721)
              ·
                rfl

theorem cell19_260954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 7].length) (baseStart_260954 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_260954 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_260954 prefixEnd_260954 := by exact prefixLift 260954
  have htrace : WordTrace (prefixWord ++ tailWord_260954) baseStart_260954 baseEnd_260954 := by
    simpa [prefixWord, tailWord_260954, baseEnd_260954] using wordTrace_append hprefix tailTrace_260954
  have hstable : (prefixWord ++ tailWord_260954).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260954).length < 2 ^ (prefixWord ++ tailWord_260954).sum := by decide
  have hdescent : baseEnd_260954 < baseStart_260954 := by decide
  rcases family_descends (prefixWord ++ tailWord_260954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261026 : List Nat := [3, 3, 1, 2, 2, 3, 1, 4]
def baseStart_261026 : Nat := 118140960795 + 261026 * 2 ^ 59
def prefixEnd_261026 : Nat := 4983230072969 + 3 ^ 40 * 261026 * 2
def baseEnd_261026 : Nat := 79426252634430203421967

theorem tailTrace_261026 : CollatzResearch.WordTrace tailWord_261026 prefixEnd_261026 79426252634430203421967 := by
  unfold tailWord_261026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2380100088088714134184733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6346933568236571024492621 2380100088088714134184733)
  ·
    refine ⟨892537533033267800319275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2380100088088714134184733 892537533033267800319275)
    ·
      refine ⟨1338806299549901700478913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 892537533033267800319275 1338806299549901700478913)
      ·
        refine ⟨1004104724662426275359185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1338806299549901700478913 1004104724662426275359185)
        ·
          refine ⟨753078543496819706519389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1004104724662426275359185 753078543496819706519389)
          ·
            refine ⟨282404453811307389944771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 753078543496819706519389 282404453811307389944771)
            ·
              refine ⟨423606680716961084917157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282404453811307389944771 423606680716961084917157)
              ·
                refine ⟨79426252634430203421967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423606680716961084917157 79426252634430203421967)
                ·
                  rfl

theorem cell19_261026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_261026 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261026 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261026 prefixEnd_261026 := by exact prefixLift 261026
  have htrace : WordTrace (prefixWord ++ tailWord_261026) baseStart_261026 baseEnd_261026 := by
    simpa [prefixWord, tailWord_261026, baseEnd_261026] using wordTrace_append hprefix tailTrace_261026
  have hstable : (prefixWord ++ tailWord_261026).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261026).length < 2 ^ (prefixWord ++ tailWord_261026).sum := by decide
  have hdescent : baseEnd_261026 < baseStart_261026 := by decide
  rcases family_descends (prefixWord ++ tailWord_261026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261068 : List Nat := [2, 2, 1, 4, 1, 1, 8]
def baseStart_261068 : Nat := 118140960795 + 261068 * 2 ^ 59
def prefixEnd_261068 : Nat := 4983230072969 + 3 ^ 40 * 261068 * 2
def baseEnd_261068 : Nat := 26479677532462183496173

theorem tailTrace_261068 : CollatzResearch.WordTrace tailWord_261068 prefixEnd_261068 26479677532462183496173 := by
  unfold tailWord_261068
  simp only [CollatzResearch.WordTrace]
  refine ⟨4760966109101348854883929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6347954812135131806511905 4760966109101348854883929)
  ·
    refine ⟨3570724581826011641162947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4760966109101348854883929 3570724581826011641162947)
    ·
      refine ⟨5356086872739017461744421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3570724581826011641162947 5356086872739017461744421)
      ·
        refine ⟨1004266288638565774077079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5356086872739017461744421 1004266288638565774077079)
        ·
          refine ⟨1506399432957848661115619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004266288638565774077079 1506399432957848661115619)
          ·
            refine ⟨2259599149436772991673429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506399432957848661115619 2259599149436772991673429)
            ·
              refine ⟨26479677532462183496173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2259599149436772991673429 26479677532462183496173)
              ·
                rfl

theorem cell19_261068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 8].length) (baseStart_261068 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261068 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261068 prefixEnd_261068 := by exact prefixLift 261068
  have htrace : WordTrace (prefixWord ++ tailWord_261068) baseStart_261068 baseEnd_261068 := by
    simpa [prefixWord, tailWord_261068, baseEnd_261068] using wordTrace_append hprefix tailTrace_261068
  have hstable : (prefixWord ++ tailWord_261068).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261068).length < 2 ^ (prefixWord ++ tailWord_261068).sum := by decide
  have hdescent : baseEnd_261068 < baseStart_261068 := by decide
  rcases family_descends (prefixWord ++ tailWord_261068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261144 : List Nat := [2, 1, 2, 3, 2, 2, 1, 6]
def baseStart_261144 : Nat := 118140960795 + 261144 * 2 ^ 59
def prefixEnd_261144 : Nat := 4983230072969 + 3 ^ 40 * 261144 * 2
def baseEnd_261144 : Nat := 79462158244640892799423

theorem tailTrace_261144 : CollatzResearch.WordTrace tailWord_261144 prefixEnd_261144 79462158244640892799423 := by
  unfold tailWord_261144
  simp only [CollatzResearch.WordTrace]
  refine ⟨4762352082963681344767243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6349802777284908459689657 4762352082963681344767243)
  ·
    refine ⟨7143528124445522017150865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4762352082963681344767243 7143528124445522017150865)
    ·
      refine ⟨5357646093334141512863149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7143528124445522017150865 5357646093334141512863149)
      ·
        refine ⟨2009117285000303067323681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5357646093334141512863149 2009117285000303067323681)
        ·
          refine ⟨1506837963750227300492761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2009117285000303067323681 1506837963750227300492761)
          ·
            refine ⟨1130128472812670475369571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1506837963750227300492761 1130128472812670475369571)
            ·
              refine ⟨1695192709219005713054357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130128472812670475369571 1695192709219005713054357)
              ·
                refine ⟨79462158244640892799423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1695192709219005713054357 79462158244640892799423)
                ·
                  rfl

theorem cell19_261144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_261144 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261144 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261144 prefixEnd_261144 := by exact prefixLift 261144
  have htrace : WordTrace (prefixWord ++ tailWord_261144) baseStart_261144 baseEnd_261144 := by
    simpa [prefixWord, tailWord_261144, baseEnd_261144] using wordTrace_append hprefix tailTrace_261144
  have hstable : (prefixWord ++ tailWord_261144).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261144).length < 2 ^ (prefixWord ++ tailWord_261144).sum := by decide
  have hdescent : baseEnd_261144 < baseStart_261144 := by decide
  rcases family_descends (prefixWord ++ tailWord_261144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261197 : List Nat := [1, 6, 1, 1, 1, 4, 1, 4]
def baseStart_261197 : Nat := 118140960795 + 261197 * 2 ^ 59
def prefixEnd_261197 : Nat := 4983230072969 + 3 ^ 40 * 261197 * 2
def baseEnd_261197 : Nat := 79478285340752473621501

theorem tailTrace_261197 : CollatzResearch.WordTrace tailWord_261197 prefixEnd_261197 79478285340752473621501 := by
  unfold tailWord_261197
  simp only [CollatzResearch.WordTrace]
  refine ⟨9526637234735352741213845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6351091489823568494142563 9526637234735352741213845)
  ·
    refine ⟨446561120378219659744399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9526637234735352741213845 446561120378219659744399)
    ·
      refine ⟨669841680567329489616599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446561120378219659744399 669841680567329489616599)
      ·
        refine ⟨1004762520850994234424899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669841680567329489616599 1004762520850994234424899)
        ·
          refine ⟨1507143781276491351637349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004762520850994234424899 1507143781276491351637349)
          ·
            refine ⟨282589458989342128432003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1507143781276491351637349 282589458989342128432003)
            ·
              refine ⟨423884188484013192648005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282589458989342128432003 423884188484013192648005)
              ·
                refine ⟨79478285340752473621501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423884188484013192648005 79478285340752473621501)
                ·
                  rfl

theorem cell19_261197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 4].length) (baseStart_261197 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261197 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261197 prefixEnd_261197 := by exact prefixLift 261197
  have htrace : WordTrace (prefixWord ++ tailWord_261197) baseStart_261197 baseEnd_261197 := by
    simpa [prefixWord, tailWord_261197, baseEnd_261197] using wordTrace_append hprefix tailTrace_261197
  have hstable : (prefixWord ++ tailWord_261197).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261197).length < 2 ^ (prefixWord ++ tailWord_261197).sum := by decide
  have hdescent : baseEnd_261197 < baseStart_261197 := by decide
  rcases family_descends (prefixWord ++ tailWord_261197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261201 : List Nat := [1, 2, 2, 1, 3, 1, 5, 4]
def baseStart_261201 : Nat := 118140960795 + 261201 * 2 ^ 59
def prefixEnd_261201 : Nat := 4983230072969 + 3 ^ 40 * 261201 * 2
def baseEnd_261201 : Nat := 79479502480081649532601

theorem tailTrace_261201 : CollatzResearch.WordTrace tailWord_261201 prefixEnd_261201 79479502480081649532601 := by
  unfold tailWord_261201
  simp only [CollatzResearch.WordTrace]
  refine ⟨9526783126720861424359457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6351188751147240949572971 9526783126720861424359457)
  ·
    refine ⟨7145087345040646068269593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9526783126720861424359457 7145087345040646068269593)
    ·
      refine ⟨5358815508780484551202195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7145087345040646068269593 5358815508780484551202195)
      ·
        refine ⟨8038223263170726826803293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5358815508780484551202195 8038223263170726826803293)
        ·
          refine ⟨3014333723689022560051235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8038223263170726826803293 3014333723689022560051235)
          ·
            refine ⟨4521500585533533840076853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3014333723689022560051235 4521500585533533840076853)
            ·
              refine ⟨423890679893768797507205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4521500585533533840076853 423890679893768797507205)
              ·
                refine ⟨79479502480081649532601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423890679893768797507205 79479502480081649532601)
                ·
                  rfl

theorem cell19_261201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_261201 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261201 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261201 prefixEnd_261201 := by exact prefixLift 261201
  have htrace : WordTrace (prefixWord ++ tailWord_261201) baseStart_261201 baseEnd_261201 := by
    simpa [prefixWord, tailWord_261201, baseEnd_261201] using wordTrace_append hprefix tailTrace_261201
  have hstable : (prefixWord ++ tailWord_261201).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261201).length < 2 ^ (prefixWord ++ tailWord_261201).sum := by decide
  have hdescent : baseEnd_261201 < baseStart_261201 := by decide
  rcases family_descends (prefixWord ++ tailWord_261201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261258 : List Nat := [3, 1, 2, 3, 1, 1, 2, 6]
def baseStart_261258 : Nat := 118140960795 + 261258 * 2 ^ 59
def prefixEnd_261258 : Nat := 4983230072969 + 3 ^ 40 * 261258 * 2
def baseEnd_261258 : Nat := 79496846715522406265779

theorem tailTrace_261258 : CollatzResearch.WordTrace tailWord_261258 prefixEnd_261258 79496846715522406265779 := by
  unfold tailWord_261258
  simp only [CollatzResearch.WordTrace]
  refine ⟨2382215521878590039796107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6352574725009573439456285 2382215521878590039796107)
  ·
    refine ⟨3573323282817885059694161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2382215521878590039796107 3573323282817885059694161)
    ·
      refine ⟨2679992462113413794770621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3573323282817885059694161 2679992462113413794770621)
      ·
        refine ⟨1004997173292530173038983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2679992462113413794770621 1004997173292530173038983)
        ·
          refine ⟨1507495759938795259558475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004997173292530173038983 1507495759938795259558475)
          ·
            refine ⟨2261243639908192889337713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507495759938795259558475 2261243639908192889337713)
            ·
              refine ⟨1695932729931144667003285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2261243639908192889337713 1695932729931144667003285)
              ·
                refine ⟨79496846715522406265779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1695932729931144667003285 79496846715522406265779)
                ·
                  rfl

theorem cell19_261258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_261258 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261258 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261258 prefixEnd_261258 := by exact prefixLift 261258
  have htrace : WordTrace (prefixWord ++ tailWord_261258) baseStart_261258 baseEnd_261258 := by
    simpa [prefixWord, tailWord_261258, baseEnd_261258] using wordTrace_append hprefix tailTrace_261258
  have hstable : (prefixWord ++ tailWord_261258).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261258).length < 2 ^ (prefixWord ++ tailWord_261258).sum := by decide
  have hdescent : baseEnd_261258 < baseStart_261258 := by decide
  rcases family_descends (prefixWord ++ tailWord_261258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261277 : List Nat := [1, 4, 2, 1, 1, 2, 3, 5]
def baseStart_261277 : Nat := 118140960795 + 261277 * 2 ^ 59
def prefixEnd_261277 : Nat := 4983230072969 + 3 ^ 40 * 261277 * 2
def baseEnd_261277 : Nat := 79502628127335991843505

theorem tailTrace_261277 : CollatzResearch.WordTrace tailWord_261277 prefixEnd_261277 79502628127335991843505 := by
  unfold tailWord_261277
  simp only [CollatzResearch.WordTrace]
  refine ⟨9529555074445526404126085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6353036716297017602750723 9529555074445526404126085)
  ·
    refine ⟨1786791576458536200773641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9529555074445526404126085 1786791576458536200773641)
    ·
      refine ⟨1340093682343902150580231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1786791576458536200773641 1340093682343902150580231)
      ·
        refine ⟨2010140523515853225870347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1340093682343902150580231 2010140523515853225870347)
        ·
          refine ⟨3015210785273779838805521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2010140523515853225870347 3015210785273779838805521)
          ·
            refine ⟨2261408088955334879104141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3015210785273779838805521 2261408088955334879104141)
            ·
              refine ⟨848028033358250579664053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2261408088955334879104141 848028033358250579664053)
              ·
                refine ⟨79502628127335991843505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 848028033358250579664053 79502628127335991843505)
                ·
                  rfl

theorem cell19_261277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_261277 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261277 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261277 prefixEnd_261277 := by exact prefixLift 261277
  have htrace : WordTrace (prefixWord ++ tailWord_261277) baseStart_261277 baseEnd_261277 := by
    simpa [prefixWord, tailWord_261277, baseEnd_261277] using wordTrace_append hprefix tailTrace_261277
  have hstable : (prefixWord ++ tailWord_261277).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261277).length < 2 ^ (prefixWord ++ tailWord_261277).sum := by decide
  have hdescent : baseEnd_261277 < baseStart_261277 := by decide
  rcases family_descends (prefixWord ++ tailWord_261277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261313 : List Nat := [1, 2, 6, 1, 1, 1, 1, 6]
def baseStart_261313 : Nat := 118140960795 + 261313 * 2 ^ 59
def prefixEnd_261313 : Nat := 4983230072969 + 3 ^ 40 * 261313 * 2
def baseEnd_261313 : Nat := 79513582381298575043407

theorem tailTrace_261313 : CollatzResearch.WordTrace tailWord_261313 prefixEnd_261313 79513582381298575043407 := by
  unfold tailWord_261313
  simp only [CollatzResearch.WordTrace]
  refine ⟨9530868102315104552436593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6353912068210069701624395 9530868102315104552436593)
  ·
    refine ⟨7148151076736328414327445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9530868102315104552436593 7148151076736328414327445)
    ·
      refine ⟨335069581722015394421599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7148151076736328414327445 335069581722015394421599)
      ·
        refine ⟨502604372583023091632399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335069581722015394421599 502604372583023091632399)
        ·
          refine ⟨753906558874534637448599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502604372583023091632399 753906558874534637448599)
          ·
            refine ⟨1130859838311801956172899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753906558874534637448599 1130859838311801956172899)
            ·
              refine ⟨1696289757467702934259349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130859838311801956172899 1696289757467702934259349)
              ·
                refine ⟨79513582381298575043407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1696289757467702934259349 79513582381298575043407)
                ·
                  rfl

theorem cell19_261313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 6].length) (baseStart_261313 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261313 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261313 prefixEnd_261313 := by exact prefixLift 261313
  have htrace : WordTrace (prefixWord ++ tailWord_261313) baseStart_261313 baseEnd_261313 := by
    simpa [prefixWord, tailWord_261313, baseEnd_261313] using wordTrace_append hprefix tailTrace_261313
  have hstable : (prefixWord ++ tailWord_261313).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261313).length < 2 ^ (prefixWord ++ tailWord_261313).sum := by decide
  have hdescent : baseEnd_261313 < baseStart_261313 := by decide
  rcases family_descends (prefixWord ++ tailWord_261313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261351 : List Nat := [1, 1, 5, 3, 3, 6]
def baseStart_261351 : Nat := 118140960795 + 261351 * 2 ^ 59
def prefixEnd_261351 : Nat := 4983230072969 + 3 ^ 40 * 261351 * 2
def baseEnd_261351 : Nat := 8836127244991749577651

theorem tailTrace_261351 : CollatzResearch.WordTrace tailWord_261351 prefixEnd_261351 8836127244991749577651 := by
  unfold tailWord_261351
  simp only [CollatzResearch.WordTrace]
  refine ⟨9532254076177437042319907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6354836050784958028213271 9532254076177437042319907)
  ·
    refine ⟨14298381114266155563479861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9532254076177437042319907 14298381114266155563479861)
    ·
      refine ⟨1340473229462452084076237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14298381114266155563479861 1340473229462452084076237)
      ·
        refine ⟨502677461048419531528589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1340473229462452084076237 502677461048419531528589)
        ·
          refine ⟨188504047893157324323221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 502677461048419531528589 188504047893157324323221)
          ·
            refine ⟨8836127244991749577651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188504047893157324323221 8836127244991749577651)
            ·
              rfl

theorem cell19_261351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 6].length) (baseStart_261351 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261351 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261351 prefixEnd_261351 := by exact prefixLift 261351
  have htrace : WordTrace (prefixWord ++ tailWord_261351) baseStart_261351 baseEnd_261351 := by
    simpa [prefixWord, tailWord_261351, baseEnd_261351] using wordTrace_append hprefix tailTrace_261351
  have hstable : (prefixWord ++ tailWord_261351).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261351).length < 2 ^ (prefixWord ++ tailWord_261351).sum := by decide
  have hdescent : baseEnd_261351 < baseStart_261351 := by decide
  rcases family_descends (prefixWord ++ tailWord_261351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261355 : List Nat := [1, 1, 1, 1, 2, 13]
def baseStart_261355 : Nat := 118140960795 + 261355 * 2 ^ 59
def prefixEnd_261355 : Nat := 4983230072969 + 3 ^ 40 * 261355 * 2
def baseEnd_261355 : Nat := 8836262482694991345551

theorem tailTrace_261355 : CollatzResearch.WordTrace tailWord_261355 prefixEnd_261355 8836262482694991345551 := by
  unfold tailWord_261355
  simp only [CollatzResearch.WordTrace]
  refine ⟨9532399968162945725465519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6354933312108630483643679 9532399968162945725465519)
  ·
    refine ⟨14298599952244418588198279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9532399968162945725465519 14298599952244418588198279)
    ·
      refine ⟨21447899928366627882297419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14298599952244418588198279 21447899928366627882297419)
      ·
        refine ⟨32171849892549941823446129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21447899928366627882297419 32171849892549941823446129)
        ·
          refine ⟨24128887419412456367584597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32171849892549941823446129 24128887419412456367584597)
          ·
            refine ⟨8836262482694991345551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 24128887419412456367584597 8836262482694991345551)
            ·
              rfl

theorem cell19_261355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 13].length) (baseStart_261355 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261355 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261355 prefixEnd_261355 := by exact prefixLift 261355
  have htrace : WordTrace (prefixWord ++ tailWord_261355) baseStart_261355 baseEnd_261355 := by
    simpa [prefixWord, tailWord_261355, baseEnd_261355] using wordTrace_append hprefix tailTrace_261355
  have hstable : (prefixWord ++ tailWord_261355).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261355).length < 2 ^ (prefixWord ++ tailWord_261355).sum := by decide
  have hdescent : baseEnd_261355 < baseStart_261355 := by decide
  rcases family_descends (prefixWord ++ tailWord_261355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261364 : List Nat := [2, 6, 1, 2, 1, 2, 1, 4]
def baseStart_261364 : Nat := 118140960795 + 261364 * 2 ^ 59
def prefixEnd_261364 : Nat := 4983230072969 + 3 ^ 40 * 261364 * 2
def baseEnd_261364 : Nat := 79529100907745567909935

theorem tailTrace_261364 : CollatzResearch.WordTrace tailWord_261364 prefixEnd_261364 79529100907745567909935 := by
  unfold tailWord_261364
  simp only [CollatzResearch.WordTrace]
  refine ⟨4766364112565170131271573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6355152150086893508362097 4766364112565170131271573)
  ·
    refine ⟨223423317776492349903355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4766364112565170131271573 223423317776492349903355)
    ·
      refine ⟨335134976664738524855033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223423317776492349903355 335134976664738524855033)
      ·
        refine ⟨251351232498553893641275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335134976664738524855033 251351232498553893641275)
        ·
          refine ⟨377026848747830840461913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251351232498553893641275 377026848747830840461913)
          ·
            refine ⟨282770136560873130346435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377026848747830840461913 282770136560873130346435)
            ·
              refine ⟨424155204841309695519653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282770136560873130346435 424155204841309695519653)
              ·
                refine ⟨79529100907745567909935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 424155204841309695519653 79529100907745567909935)
                ·
                  rfl

theorem cell19_261364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_261364 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261364 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261364 prefixEnd_261364 := by exact prefixLift 261364
  have htrace : WordTrace (prefixWord ++ tailWord_261364) baseStart_261364 baseEnd_261364 := by
    simpa [prefixWord, tailWord_261364, baseEnd_261364] using wordTrace_append hprefix tailTrace_261364
  have hstable : (prefixWord ++ tailWord_261364).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261364).length < 2 ^ (prefixWord ++ tailWord_261364).sum := by decide
  have hdescent : baseEnd_261364 < baseStart_261364 := by decide
  rcases family_descends (prefixWord ++ tailWord_261364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261406 : List Nat := [4, 3, 2, 1, 2, 1, 6]
def baseStart_261406 : Nat := 118140960795 + 261406 * 2 ^ 59
def prefixEnd_261406 : Nat := 4983230072969 + 3 ^ 40 * 261406 * 2
def baseEnd_261406 : Nat := 26513960290233971658829

theorem tailTrace_261406 : CollatzResearch.WordTrace tailWord_261406 prefixEnd_261406 26513960290233971658829 := by
  unfold tailWord_261406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1191782511372272679446509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6356173393985454290381381 1191782511372272679446509)
  ·
    refine ⟨446918441764602254792441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1191782511372272679446509 446918441764602254792441)
    ·
      refine ⟨335188831323451691094331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446918441764602254792441 335188831323451691094331)
      ·
        refine ⟨502783246985177536641497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335188831323451691094331 502783246985177536641497)
        ·
          refine ⟨377087435238883152481123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502783246985177536641497 377087435238883152481123)
          ·
            refine ⟨565631152858324728721685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377087435238883152481123 565631152858324728721685)
            ·
              refine ⟨26513960290233971658829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 565631152858324728721685 26513960290233971658829)
              ·
                rfl

theorem cell19_261406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 6].length) (baseStart_261406 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261406 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261406 prefixEnd_261406 := by exact prefixLift 261406
  have htrace : WordTrace (prefixWord ++ tailWord_261406) baseStart_261406 baseEnd_261406 := by
    simpa [prefixWord, tailWord_261406, baseEnd_261406] using wordTrace_append hprefix tailTrace_261406
  have hstable : (prefixWord ++ tailWord_261406).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261406).length < 2 ^ (prefixWord ++ tailWord_261406).sum := by decide
  have hdescent : baseEnd_261406 < baseStart_261406 := by decide
  rcases family_descends (prefixWord ++ tailWord_261406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261444 : List Nat := [2, 3, 4, 1, 1, 1, 4, 3]
def baseStart_261444 : Nat := 118140960795 + 261444 * 2 ^ 59
def prefixEnd_261444 : Nat := 4983230072969 + 3 ^ 40 * 261444 * 2
def baseEnd_261444 : Nat := 79553443694329086131939

theorem tailTrace_261444 : CollatzResearch.WordTrace tailWord_261444 prefixEnd_261444 79553443694329086131939 := by
  unfold tailWord_261444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4767823032420256962727693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6357097376560342616970257 4767823032420256962727693)
  ·
    refine ⟨1787933637157596361022885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4767823032420256962727693 1787933637157596361022885)
    ·
      refine ⟨335237556967049317691791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1787933637157596361022885 335237556967049317691791)
      ·
        refine ⟨502856335450573976537687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335237556967049317691791 502856335450573976537687)
        ·
          refine ⟨754284503175860964806531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502856335450573976537687 754284503175860964806531)
          ·
            refine ⟨1131426754763791447209797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754284503175860964806531 1131426754763791447209797)
            ·
              refine ⟨212142516518210896351837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1131426754763791447209797 212142516518210896351837)
              ·
                refine ⟨79553443694329086131939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212142516518210896351837 79553443694329086131939)
                ·
                  rfl

theorem cell19_261444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_261444 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261444 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261444 prefixEnd_261444 := by exact prefixLift 261444
  have htrace : WordTrace (prefixWord ++ tailWord_261444) baseStart_261444 baseEnd_261444 := by
    simpa [prefixWord, tailWord_261444, baseEnd_261444] using wordTrace_append hprefix tailTrace_261444
  have hstable : (prefixWord ++ tailWord_261444).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261444).length < 2 ^ (prefixWord ++ tailWord_261444).sum := by decide
  have hdescent : baseEnd_261444 < baseStart_261444 := by decide
  rcases family_descends (prefixWord ++ tailWord_261444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261522 : List Nat := [3, 2, 3, 3, 1, 7]
def baseStart_261522 : Nat := 118140960795 + 261522 * 2 ^ 59
def prefixEnd_261522 : Nat := 4983230072969 + 3 ^ 40 * 261522 * 2
def baseEnd_261522 : Nat := 8841908656805335155377

theorem tailTrace_261522 : CollatzResearch.WordTrace tailWord_261522 prefixEnd_261522 8841908656805335155377 := by
  unfold tailWord_261522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2384622739639483311698705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6358993972371955497863213 2384622739639483311698705)
  ·
    refine ⟨1788467054729612483774029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2384622739639483311698705 1788467054729612483774029)
    ·
      refine ⟨670675145523604681415261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1788467054729612483774029 670675145523604681415261)
      ·
        refine ⟨251503179571351755530723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 670675145523604681415261 251503179571351755530723)
        ·
          refine ⟨377254769357027633296085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251503179571351755530723 377254769357027633296085)
          ·
            refine ⟨8841908656805335155377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 377254769357027633296085 8841908656805335155377)
            ·
              rfl

theorem cell19_261522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 7].length) (baseStart_261522 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261522 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261522 prefixEnd_261522 := by exact prefixLift 261522
  have htrace : WordTrace (prefixWord ++ tailWord_261522) baseStart_261522 baseEnd_261522 := by
    simpa [prefixWord, tailWord_261522, baseEnd_261522] using wordTrace_append hprefix tailTrace_261522
  have hstable : (prefixWord ++ tailWord_261522).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261522).length < 2 ^ (prefixWord ++ tailWord_261522).sum := by decide
  have hdescent : baseEnd_261522 < baseStart_261522 := by decide
  rcases family_descends (prefixWord ++ tailWord_261522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261524 : List Nat := [2, 4, 2, 1, 2, 8]
def baseStart_261524 : Nat := 118140960795 + 261524 * 2 ^ 59
def prefixEnd_261524 : Nat := 4983230072969 + 3 ^ 40 * 261524 * 2
def baseEnd_261524 : Nat := 8841976275656956039327

theorem tailTrace_261524 : CollatzResearch.WordTrace tailWord_261524 prefixEnd_261524 8841976275656956039327 := by
  unfold tailWord_261524
  simp only [CollatzResearch.WordTrace]
  refine ⟨4769281952275343794183813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6359042603033791725578417 4769281952275343794183813)
  ·
    refine ⟨894240366051626961409465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4769281952275343794183813 894240366051626961409465)
    ·
      refine ⟨670680274538720221057099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 894240366051626961409465 670680274538720221057099)
      ·
        refine ⟨1006020411808080331585649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670680274538720221057099 1006020411808080331585649)
        ·
          refine ⟨754515308856060248689237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1006020411808080331585649 754515308856060248689237)
          ·
            refine ⟨8841976275656956039327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 754515308856060248689237 8841976275656956039327)
            ·
              rfl

theorem cell19_261524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 8].length) (baseStart_261524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261524 prefixEnd_261524 := by exact prefixLift 261524
  have htrace : WordTrace (prefixWord ++ tailWord_261524) baseStart_261524 baseEnd_261524 := by
    simpa [prefixWord, tailWord_261524, baseEnd_261524] using wordTrace_append hprefix tailTrace_261524
  have hstable : (prefixWord ++ tailWord_261524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261524).length < 2 ^ (prefixWord ++ tailWord_261524).sum := by decide
  have hdescent : baseEnd_261524 < baseStart_261524 := by decide
  rcases family_descends (prefixWord ++ tailWord_261524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261613 : List Nat := [1, 5, 1, 3, 3, 1, 2, 3]
def baseStart_261613 : Nat := 118140960795 + 261613 * 2 ^ 59
def prefixEnd_261613 : Nat := 4983230072969 + 3 ^ 40 * 261613 * 2
def baseEnd_261613 : Nat := 79604867830986768375923

theorem tailTrace_261613 : CollatzResearch.WordTrace tailWord_261613 prefixEnd_261613 79604867830986768375923 := by
  unfold tailWord_261613
  simp only [CollatzResearch.WordTrace]
  refine ⟨9541810001228255788357493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6361206667485503858904995 9541810001228255788357493)
  ·
    refine ⟨894544687615148980158515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9541810001228255788357493 894544687615148980158515)
    ·
      refine ⟨1341817031422723470237773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 894544687615148980158515 1341817031422723470237773)
      ·
        refine ⟨503181386783521301339165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1341817031422723470237773 503181386783521301339165)
        ·
          refine ⟨188693020043820488002187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 503181386783521301339165 188693020043820488002187)
          ·
            refine ⟨283039530065730732003281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188693020043820488002187 283039530065730732003281)
            ·
              refine ⟨212279647549298049002461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283039530065730732003281 212279647549298049002461)
              ·
                refine ⟨79604867830986768375923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212279647549298049002461 79604867830986768375923)
                ·
                  rfl

theorem cell19_261613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 3].length) (baseStart_261613 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261613 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261613 prefixEnd_261613 := by exact prefixLift 261613
  have htrace : WordTrace (prefixWord ++ tailWord_261613) baseStart_261613 baseEnd_261613 := by
    simpa [prefixWord, tailWord_261613, baseEnd_261613] using wordTrace_append hprefix tailTrace_261613
  have hstable : (prefixWord ++ tailWord_261613).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261613).length < 2 ^ (prefixWord ++ tailWord_261613).sum := by decide
  have hdescent : baseEnd_261613 < baseStart_261613 := by decide
  rcases family_descends (prefixWord ++ tailWord_261613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261617 : List Nat := [1, 2, 2, 2, 3, 4, 2, 3]
def baseStart_261617 : Nat := 118140960795 + 261617 * 2 ^ 59
def prefixEnd_261617 : Nat := 4983230072969 + 3 ^ 40 * 261617 * 2
def baseEnd_261617 : Nat := 79606084970315944287023

theorem tailTrace_261617 : CollatzResearch.WordTrace tailWord_261617 prefixEnd_261617 79606084970315944287023 := by
  unfold tailWord_261617
  simp only [CollatzResearch.WordTrace]
  refine ⟨9541955893213764471503105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6361303928809176314335403 9541955893213764471503105)
  ·
    refine ⟨7156466919910323353627329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9541955893213764471503105 7156466919910323353627329)
    ·
      refine ⟨5367350189932742515220497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7156466919910323353627329 5367350189932742515220497)
      ·
        refine ⟨4025512642449556886415373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5367350189932742515220497 4025512642449556886415373)
        ·
          refine ⟨1509567240918583832405765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4025512642449556886415373 1509567240918583832405765)
          ·
            refine ⟨283043857672234468576081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1509567240918583832405765 283043857672234468576081)
            ·
              refine ⟨212282893254175851432061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283043857672234468576081 212282893254175851432061)
              ·
                refine ⟨79606084970315944287023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212282893254175851432061 79606084970315944287023)
                ·
                  rfl

theorem cell19_261617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 3].length) (baseStart_261617 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261617 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261617 prefixEnd_261617 := by exact prefixLift 261617
  have htrace : WordTrace (prefixWord ++ tailWord_261617) baseStart_261617 baseEnd_261617 := by
    simpa [prefixWord, tailWord_261617, baseEnd_261617] using wordTrace_append hprefix tailTrace_261617
  have hstable : (prefixWord ++ tailWord_261617).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261617).length < 2 ^ (prefixWord ++ tailWord_261617).sum := by decide
  have hdescent : baseEnd_261617 < baseStart_261617 := by decide
  rcases family_descends (prefixWord ++ tailWord_261617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261636 : List Nat := [2, 3, 2, 3, 2, 2, 5]
def baseStart_261636 : Nat := 118140960795 + 261636 * 2 ^ 59
def prefixEnd_261636 : Nat := 4983230072969 + 3 ^ 40 * 261636 * 2
def baseEnd_261636 : Nat := 26537288794043176621583

theorem tailTrace_261636 : CollatzResearch.WordTrace tailWord_261636 prefixEnd_261636 26537288794043176621583 := by
  unfold tailWord_261636
  simp only [CollatzResearch.WordTrace]
  refine ⟨4771324440072465358222381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6361765920096620477629841 4771324440072465358222381)
  ·
    refine ⟨1789246665027174509333393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4771324440072465358222381 1789246665027174509333393)
    ·
      refine ⟨1341934998770380882000045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1789246665027174509333393 1341934998770380882000045)
      ·
        refine ⟨503225624538892830750017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1341934998770380882000045 503225624538892830750017)
        ·
          refine ⟨377419218404169623062513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503225624538892830750017 377419218404169623062513)
          ·
            refine ⟨283064413803127217296885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377419218404169623062513 283064413803127217296885)
            ·
              refine ⟨26537288794043176621583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 283064413803127217296885 26537288794043176621583)
              ·
                rfl

theorem cell19_261636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 5].length) (baseStart_261636 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261636 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261636 prefixEnd_261636 := by exact prefixLift 261636
  have htrace : WordTrace (prefixWord ++ tailWord_261636) baseStart_261636 baseEnd_261636 := by
    simpa [prefixWord, tailWord_261636, baseEnd_261636] using wordTrace_append hprefix tailTrace_261636
  have hstable : (prefixWord ++ tailWord_261636).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261636).length < 2 ^ (prefixWord ++ tailWord_261636).sum := by decide
  have hdescent : baseEnd_261636 < baseStart_261636 := by decide
  rcases family_descends (prefixWord ++ tailWord_261636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261640 : List Nat := [2, 1, 3, 2, 1, 1, 9]
def baseStart_261640 : Nat := 118140960795 + 261640 * 2 ^ 59
def prefixEnd_261640 : Nat := 4983230072969 + 3 ^ 40 * 261640 * 2
def baseEnd_261640 : Nat := 26537694507152901925283

theorem tailTrace_261640 : CollatzResearch.WordTrace tailWord_261640 prefixEnd_261640 26537694507152901925283 := by
  unfold tailWord_261640
  simp only [CollatzResearch.WordTrace]
  refine ⟨4771397386065219699795187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6361863181420292933060249 4771397386065219699795187)
  ·
    refine ⟨7157096079097829549692781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4771397386065219699795187 7157096079097829549692781)
    ·
      refine ⟨2683911029661686081134793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7157096079097829549692781 2683911029661686081134793)
      ·
        refine ⟨2012933272246264560851095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2683911029661686081134793 2012933272246264560851095)
        ·
          refine ⟨3019399908369396841276643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2012933272246264560851095 3019399908369396841276643)
          ·
            refine ⟨4529099862554095261914965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3019399908369396841276643 4529099862554095261914965)
            ·
              refine ⟨26537694507152901925283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4529099862554095261914965 26537694507152901925283)
              ·
                rfl

theorem cell19_261640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 9].length) (baseStart_261640 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261640 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261640 prefixEnd_261640 := by exact prefixLift 261640
  have htrace : WordTrace (prefixWord ++ tailWord_261640) baseStart_261640 baseEnd_261640 := by
    simpa [prefixWord, tailWord_261640, baseEnd_261640] using wordTrace_append hprefix tailTrace_261640
  have hstable : (prefixWord ++ tailWord_261640).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261640).length < 2 ^ (prefixWord ++ tailWord_261640).sum := by decide
  have hdescent : baseEnd_261640 < baseStart_261640 := by decide
  rcases family_descends (prefixWord ++ tailWord_261640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261714 : List Nat := [3, 2, 2, 1, 2, 2, 3, 4]
def baseStart_261714 : Nat := 118140960795 + 261714 * 2 ^ 59
def prefixEnd_261714 : Nat := 4983230072969 + 3 ^ 40 * 261714 * 2
def baseEnd_261714 : Nat := 79635600599048460131203

theorem tailTrace_261714 : CollatzResearch.WordTrace tailWord_261714 prefixEnd_261714 79635600599048460131203 := by
  unfold tailWord_261714
  simp only [CollatzResearch.WordTrace]
  refine ⟨2386373443465587509446049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6363662515908233358522797 2386373443465587509446049)
  ·
    refine ⟨1789780082599190632084537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2386373443465587509446049 1789780082599190632084537)
    ·
      refine ⟨1342335061949392974063403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1789780082599190632084537 1342335061949392974063403)
      ·
        refine ⟨2013502592924089461095105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342335061949392974063403 2013502592924089461095105)
        ·
          refine ⟨1510126944693067095821329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2013502592924089461095105 1510126944693067095821329)
          ·
            refine ⟨1132595208519800321865997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1510126944693067095821329 1132595208519800321865997)
            ·
              refine ⟨424723203194925120699749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1132595208519800321865997 424723203194925120699749)
              ·
                refine ⟨79635600599048460131203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 424723203194925120699749 79635600599048460131203)
                ·
                  rfl

theorem cell19_261714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_261714 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261714 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261714 prefixEnd_261714 := by exact prefixLift 261714
  have htrace : WordTrace (prefixWord ++ tailWord_261714) baseStart_261714 baseEnd_261714 := by
    simpa [prefixWord, tailWord_261714, baseEnd_261714] using wordTrace_append hprefix tailTrace_261714
  have hstable : (prefixWord ++ tailWord_261714).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261714).length < 2 ^ (prefixWord ++ tailWord_261714).sum := by decide
  have hdescent : baseEnd_261714 < baseStart_261714 := by decide
  rcases family_descends (prefixWord ++ tailWord_261714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261735 : List Nat := [1, 1, 5, 1, 1, 1, 2, 7]
def baseStart_261735 : Nat := 118140960795 + 261735 * 2 ^ 59
def prefixEnd_261735 : Nat := 4983230072969 + 3 ^ 40 * 261735 * 2
def baseEnd_261735 : Nat := 79641990580526633664479

theorem tailTrace_261735 : CollatzResearch.WordTrace tailWord_261735 prefixEnd_261735 79641990580526633664479 := by
  unfold tailWord_261735
  simp only [CollatzResearch.WordTrace]
  refine ⟨9546259706786270624298659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6364173137857513749532439 9546259706786270624298659)
  ·
    refine ⟨14319389560179405936447989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9546259706786270624298659 14319389560179405936447989)
    ·
      refine ⟨1342442771266819306541999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14319389560179405936447989 1342442771266819306541999)
      ·
        refine ⟨2013664156900228959812999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342442771266819306541999 2013664156900228959812999)
        ·
          refine ⟨3020496235350343439719499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013664156900228959812999 3020496235350343439719499)
          ·
            refine ⟨4530744353025515159579249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3020496235350343439719499 4530744353025515159579249)
            ·
              refine ⟨3398058264769136369684437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4530744353025515159579249 3398058264769136369684437)
              ·
                refine ⟨79641990580526633664479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3398058264769136369684437 79641990580526633664479)
                ·
                  rfl

theorem cell19_261735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_261735 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261735 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261735 prefixEnd_261735 := by exact prefixLift 261735
  have htrace : WordTrace (prefixWord ++ tailWord_261735) baseStart_261735 baseEnd_261735 := by
    simpa [prefixWord, tailWord_261735, baseEnd_261735] using wordTrace_append hprefix tailTrace_261735
  have hstable : (prefixWord ++ tailWord_261735).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261735).length < 2 ^ (prefixWord ++ tailWord_261735).sum := by decide
  have hdescent : baseEnd_261735 < baseStart_261735 := by decide
  rcases family_descends (prefixWord ++ tailWord_261735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261828 : List Nat := [2, 3, 3, 1, 1, 1, 4, 4]
def baseStart_261828 : Nat := 118140960795 + 261828 * 2 ^ 59
def prefixEnd_261828 : Nat := 4983230072969 + 3 ^ 40 * 261828 * 2
def baseEnd_261828 : Nat := 79670289069929973597559

theorem tailTrace_261828 : CollatzResearch.WordTrace tailWord_261828 prefixEnd_261828 79670289069929973597559 := by
  unfold tailWord_261828
  simp only [CollatzResearch.WordTrace]
  refine ⟨4774825847724673753717069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6366434463632898338289425 4774825847724673753717069)
  ·
    refine ⟨1790559692896752657643901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4774825847724673753717069 1790559692896752657643901)
    ·
      refine ⟨671459884836282246616463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1790559692896752657643901 671459884836282246616463)
      ·
        refine ⟨1007189827254423369924695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671459884836282246616463 1007189827254423369924695)
        ·
          refine ⟨1510784740881635054887043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007189827254423369924695 1510784740881635054887043)
          ·
            refine ⟨2266177111322452582330565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510784740881635054887043 2266177111322452582330565)
            ·
              refine ⟨424908208372959859186981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2266177111322452582330565 424908208372959859186981)
              ·
                refine ⟨79670289069929973597559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 424908208372959859186981 79670289069929973597559)
                ·
                  rfl

theorem cell19_261828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_261828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261828 prefixEnd_261828 := by exact prefixLift 261828
  have htrace : WordTrace (prefixWord ++ tailWord_261828) baseStart_261828 baseEnd_261828 := by
    simpa [prefixWord, tailWord_261828, baseEnd_261828] using wordTrace_append hprefix tailTrace_261828
  have hstable : (prefixWord ++ tailWord_261828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261828).length < 2 ^ (prefixWord ++ tailWord_261828).sum := by decide
  have hdescent : baseEnd_261828 < baseStart_261828 := by decide
  rcases family_descends (prefixWord ++ tailWord_261828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261849 : List Nat := [1, 2, 1, 2, 3, 3, 2, 5]
def baseStart_261849 : Nat := 118140960795 + 261849 * 2 ^ 59
def prefixEnd_261849 : Nat := 4983230072969 + 3 ^ 40 * 261849 * 2
def baseEnd_261849 : Nat := 79676679051408147130835

theorem tailTrace_261849 : CollatzResearch.WordTrace tailWord_261849 prefixEnd_261849 79676679051408147130835 := by
  unfold tailWord_261849
  simp only [CollatzResearch.WordTrace]
  refine ⟨9550417628373268093948601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6366945085582178729299067 9550417628373268093948601)
  ·
    refine ⟨7162813221279951070461451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9550417628373268093948601 7162813221279951070461451)
    ·
      refine ⟨10744219831919926605692177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7162813221279951070461451 10744219831919926605692177)
      ·
        refine ⟨8058164873939944954269133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10744219831919926605692177 8058164873939944954269133)
        ·
          refine ⟨3021811827727479357850925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8058164873939944954269133 3021811827727479357850925)
          ·
            refine ⟨1133179435397804759194097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3021811827727479357850925 1133179435397804759194097)
            ·
              refine ⟨849884576548353569395573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133179435397804759194097 849884576548353569395573)
              ·
                refine ⟨79676679051408147130835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 849884576548353569395573 79676679051408147130835)
                ·
                  rfl

theorem cell19_261849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_261849 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261849 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261849 prefixEnd_261849 := by exact prefixLift 261849
  have htrace : WordTrace (prefixWord ++ tailWord_261849) baseStart_261849 baseEnd_261849 := by
    simpa [prefixWord, tailWord_261849, baseEnd_261849] using wordTrace_append hprefix tailTrace_261849
  have hstable : (prefixWord ++ tailWord_261849).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261849).length < 2 ^ (prefixWord ++ tailWord_261849).sum := by decide
  have hdescent : baseEnd_261849 < baseStart_261849 := by decide
  rcases family_descends (prefixWord ++ tailWord_261849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261887 : List Nat := [1, 1, 2, 2, 1, 3, 5, 4]
def baseStart_261887 : Nat := 118140960795 + 261887 * 2 ^ 59
def prefixEnd_261887 : Nat := 4983230072969 + 3 ^ 40 * 261887 * 2
def baseEnd_261887 : Nat := 79688241875035318286287

theorem tailTrace_261887 : CollatzResearch.WordTrace tailWord_261887 prefixEnd_261887 79688241875035318286287 := by
  unfold tailWord_261887
  simp only [CollatzResearch.WordTrace]
  refine ⟨9551803602235600583831915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6367869068157067055887943 9551803602235600583831915)
  ·
    refine ⟨14327705403353400875747873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9551803602235600583831915 14327705403353400875747873)
    ·
      refine ⟨10745779052515050656810905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14327705403353400875747873 10745779052515050656810905)
      ·
        refine ⟨8059334289386287992608179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10745779052515050656810905 8059334289386287992608179)
        ·
          refine ⟨12089001434079431988912269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8059334289386287992608179 12089001434079431988912269)
          ·
            refine ⟨4533375537779786995842101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12089001434079431988912269 4533375537779786995842101)
            ·
              refine ⟨425003956666855030860197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4533375537779786995842101 425003956666855030860197)
              ·
                refine ⟨79688241875035318286287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 425003956666855030860197 79688241875035318286287)
                ·
                  rfl

theorem cell19_261887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_261887 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261887 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261887 prefixEnd_261887 := by exact prefixLift 261887
  have htrace : WordTrace (prefixWord ++ tailWord_261887) baseStart_261887 baseEnd_261887 := by
    simpa [prefixWord, tailWord_261887, baseEnd_261887] using wordTrace_append hprefix tailTrace_261887
  have hstable : (prefixWord ++ tailWord_261887).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261887).length < 2 ^ (prefixWord ++ tailWord_261887).sum := by decide
  have hdescent : baseEnd_261887 < baseStart_261887 := by decide
  rcases family_descends (prefixWord ++ tailWord_261887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261894 : List Nat := [6, 2, 2, 1, 1, 1, 3, 3]
def baseStart_261894 : Nat := 118140960795 + 261894 * 2 ^ 59
def prefixEnd_261894 : Nat := 4983230072969 + 3 ^ 40 * 261894 * 2
def baseEnd_261894 : Nat := 79690371868861376130713

theorem tailTrace_261894 : CollatzResearch.WordTrace tailWord_261894 prefixEnd_261894 79690371868861376130713 := by
  unfold tailWord_261894
  simp only [CollatzResearch.WordTrace]
  refine ⟨298501841037820024354273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6368039275473493852891157 298501841037820024354273)
  ·
    refine ⟨223876380778365018265705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298501841037820024354273 223876380778365018265705)
    ·
      refine ⟨167907285583773763699279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223876380778365018265705 167907285583773763699279)
      ·
        refine ⟨251860928375660645548919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167907285583773763699279 251860928375660645548919)
        ·
          refine ⟨377791392563490968323379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251860928375660645548919 377791392563490968323379)
          ·
            refine ⟨566687088845236452485069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377791392563490968323379 566687088845236452485069)
            ·
              refine ⟨212507658316963669681901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 566687088845236452485069 212507658316963669681901)
              ·
                refine ⟨79690371868861376130713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212507658316963669681901 79690371868861376130713)
                ·
                  rfl

theorem cell19_261894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_261894 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261894 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261894 prefixEnd_261894 := by exact prefixLift 261894
  have htrace : WordTrace (prefixWord ++ tailWord_261894) baseStart_261894 baseEnd_261894 := by
    simpa [prefixWord, tailWord_261894, baseEnd_261894] using wordTrace_append hprefix tailTrace_261894
  have hstable : (prefixWord ++ tailWord_261894).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261894).length < 2 ^ (prefixWord ++ tailWord_261894).sum := by decide
  have hdescent : baseEnd_261894 < baseStart_261894 := by decide
  rcases family_descends (prefixWord ++ tailWord_261894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261925 : List Nat := [1, 3, 1, 2, 3, 3, 6]
def baseStart_261925 : Nat := 118140960795 + 261925 * 2 ^ 59
def prefixEnd_261925 : Nat := 4983230072969 + 3 ^ 40 * 261925 * 2
def baseEnd_261925 : Nat := 26566601566220829813913

theorem tailTrace_261925 : CollatzResearch.WordTrace tailWord_261925 prefixEnd_261925 26566601566220829813913 := by
  unfold tailWord_261925
  simp only [CollatzResearch.WordTrace]
  refine ⟨9553189576097933073715229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6368793050731955382476819 9553189576097933073715229)
  ·
    refine ⟨3582446091036724902643211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9553189576097933073715229 3582446091036724902643211)
    ·
      refine ⟨5373669136555087353964817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3582446091036724902643211 5373669136555087353964817)
      ·
        refine ⟨4030251852416315515473613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5373669136555087353964817 4030251852416315515473613)
        ·
          refine ⟨1511344444656118318302605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4030251852416315515473613 1511344444656118318302605)
          ·
            refine ⟨566754166746044369363477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1511344444656118318302605 566754166746044369363477)
            ·
              refine ⟨26566601566220829813913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 566754166746044369363477 26566601566220829813913)
              ·
                rfl

theorem cell19_261925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 6].length) (baseStart_261925 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_261925 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_261925 prefixEnd_261925 := by exact prefixLift 261925
  have htrace : WordTrace (prefixWord ++ tailWord_261925) baseStart_261925 baseEnd_261925 := by
    simpa [prefixWord, tailWord_261925, baseEnd_261925] using wordTrace_append hprefix tailTrace_261925
  have hstable : (prefixWord ++ tailWord_261925).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261925).length < 2 ^ (prefixWord ++ tailWord_261925).sum := by decide
  have hdescent : baseEnd_261925 < baseStart_261925 := by decide
  rcases family_descends (prefixWord ++ tailWord_261925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262001 : List Nat := [1, 2, 2, 2, 1, 3, 4, 4]
def baseStart_262001 : Nat := 118140960795 + 262001 * 2 ^ 59
def prefixEnd_262001 : Nat := 4983230072969 + 3 ^ 40 * 262001 * 2
def baseEnd_262001 : Nat := 79722930345916831752643

theorem tailTrace_262001 : CollatzResearch.WordTrace tailWord_262001 prefixEnd_262001 79722930345916831752643 := by
  unfold tailWord_262001
  simp only [CollatzResearch.WordTrace]
  refine ⟨9555961523822598053481857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6370641015881732035654571 9555961523822598053481857)
  ·
    refine ⟨7166971142866948540111393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9555961523822598053481857 7166971142866948540111393)
    ·
      refine ⟨5375228357150211405083545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7166971142866948540111393 5375228357150211405083545)
      ·
        refine ⟨4031421267862658553812659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5375228357150211405083545 4031421267862658553812659)
        ·
          refine ⟨6047131901793987830718989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4031421267862658553812659 6047131901793987830718989)
          ·
            refine ⟨2267674463172745436519621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6047131901793987830718989 2267674463172745436519621)
            ·
              refine ⟨425188961844889769347429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2267674463172745436519621 425188961844889769347429)
              ·
                refine ⟨79722930345916831752643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 425188961844889769347429 79722930345916831752643)
                ·
                  rfl

theorem cell19_262001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_262001 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262001 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262001 prefixEnd_262001 := by exact prefixLift 262001
  have htrace : WordTrace (prefixWord ++ tailWord_262001) baseStart_262001 baseEnd_262001 := by
    simpa [prefixWord, tailWord_262001, baseEnd_262001] using wordTrace_append hprefix tailTrace_262001
  have hstable : (prefixWord ++ tailWord_262001).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262001).length < 2 ^ (prefixWord ++ tailWord_262001).sum := by decide
  have hdescent : baseEnd_262001 < baseStart_262001 := by decide
  rcases family_descends (prefixWord ++ tailWord_262001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262020 : List Nat := [2, 3, 2, 1, 1, 1, 4, 5]
def baseStart_262020 : Nat := 118140960795 + 262020 * 2 ^ 59
def prefixEnd_262020 : Nat := 4983230072969 + 3 ^ 40 * 262020 * 2
def baseEnd_262020 : Nat := 79728711757730417330369

theorem tailTrace_262020 : CollatzResearch.WordTrace tailWord_262020 prefixEnd_262020 79728711757730417330369 := by
  unfold tailWord_262020
  simp only [CollatzResearch.WordTrace]
  refine ⟨4778327255376882149211757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6371103007169176198949009 4778327255376882149211757)
  ·
    refine ⟨1791872720766330805954409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4778327255376882149211757 1791872720766330805954409)
    ·
      refine ⟨1343904540574748104465807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1791872720766330805954409 1343904540574748104465807)
      ·
        refine ⟨2015856810862122156698711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343904540574748104465807 2015856810862122156698711)
        ·
          refine ⟨3023785216293183235048067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2015856810862122156698711 3023785216293183235048067)
          ·
            refine ⟨4535677824439774852572101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3023785216293183235048067 4535677824439774852572101)
            ·
              refine ⟨850439592082457784857269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4535677824439774852572101 850439592082457784857269)
              ·
                refine ⟨79728711757730417330369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 850439592082457784857269 79728711757730417330369)
                ·
                  rfl

theorem cell19_262020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_262020 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262020 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262020 prefixEnd_262020 := by exact prefixLift 262020
  have htrace : WordTrace (prefixWord ++ tailWord_262020) baseStart_262020 baseEnd_262020 := by
    simpa [prefixWord, tailWord_262020, baseEnd_262020] using wordTrace_append hprefix tailTrace_262020
  have hstable : (prefixWord ++ tailWord_262020).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262020).length < 2 ^ (prefixWord ++ tailWord_262020).sum := by decide
  have hdescent : baseEnd_262020 < baseStart_262020 := by decide
  rcases family_descends (prefixWord ++ tailWord_262020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262172 : List Nat := [2, 2, 3, 1, 3, 1, 1, 6]
def baseStart_262172 : Nat := 118140960795 + 262172 * 2 ^ 59
def prefixEnd_262172 : Nat := 4983230072969 + 3 ^ 40 * 262172 * 2
def baseEnd_262172 : Nat := 79774963052239101952177

theorem tailTrace_262172 : CollatzResearch.WordTrace tailWord_262172 prefixEnd_262172 79774963052239101952177 := by
  unfold tailWord_262172
  simp only [CollatzResearch.WordTrace]
  refine ⟨4781099203101547128978385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6374798937468729505304513 4781099203101547128978385)
  ·
    refine ⟨3585824402326160346733789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4781099203101547128978385 3585824402326160346733789)
    ·
      refine ⟨1344684150872310130025171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3585824402326160346733789 1344684150872310130025171)
      ·
        refine ⟨2017026226308465195037757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1344684150872310130025171 2017026226308465195037757)
        ·
          refine ⟨756384834865674448139159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2017026226308465195037757 756384834865674448139159)
          ·
            refine ⟨1134577252298511672208739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756384834865674448139159 1134577252298511672208739)
            ·
              refine ⟨1701865878447767508313109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1134577252298511672208739 1701865878447767508313109)
              ·
                refine ⟨79774963052239101952177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1701865878447767508313109 79774963052239101952177)
                ·
                  rfl

theorem cell19_262172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_262172 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262172 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262172 prefixEnd_262172 := by exact prefixLift 262172
  have htrace : WordTrace (prefixWord ++ tailWord_262172) baseStart_262172 baseEnd_262172 := by
    simpa [prefixWord, tailWord_262172, baseEnd_262172] using wordTrace_append hprefix tailTrace_262172
  have hstable : (prefixWord ++ tailWord_262172).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262172).length < 2 ^ (prefixWord ++ tailWord_262172).sum := by decide
  have hdescent : baseEnd_262172 < baseStart_262172 := by decide
  rcases family_descends (prefixWord ++ tailWord_262172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262212 : List Nat := [2, 3, 14]
def baseStart_262212 : Nat := 118140960795 + 262212 * 2 ^ 59
def prefixEnd_262212 : Nat := 4983230072969 + 3 ^ 40 * 262212 * 2
def baseEnd_262212 : Nat := 328342117059797782153

theorem tailTrace_262212 : CollatzResearch.WordTrace tailWord_262212 prefixEnd_262212 328342117059797782153 := by
  unfold tailWord_262212
  simp only [CollatzResearch.WordTrace]
  refine ⟨4781828663029090544706445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6375771550705454059608593 4781828663029090544706445)
  ·
    refine ⟨1793185748635908954264917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4781828663029090544706445 1793185748635908954264917)
    ·
      refine ⟨328342117059797782153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 1793185748635908954264917 328342117059797782153)
      ·
        rfl

theorem cell19_262212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 14].length) (baseStart_262212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262212 prefixEnd_262212 := by exact prefixLift 262212
  have htrace : WordTrace (prefixWord ++ tailWord_262212) baseStart_262212 baseEnd_262212 := by
    simpa [prefixWord, tailWord_262212, baseEnd_262212] using wordTrace_append hprefix tailTrace_262212
  have hstable : (prefixWord ++ tailWord_262212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262212).length < 2 ^ (prefixWord ++ tailWord_262212).sum := by decide
  have hdescent : baseEnd_262212 < baseStart_262212 := by decide
  rcases family_descends (prefixWord ++ tailWord_262212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262229 : List Nat := [1, 3, 2, 2, 1, 3, 3, 4]
def baseStart_262229 : Nat := 118140960795 + 262229 * 2 ^ 59
def prefixEnd_262229 : Nat := 4983230072969 + 3 ^ 40 * 262229 * 2
def baseEnd_262229 : Nat := 79792307287679858685355

theorem tailTrace_262229 : CollatzResearch.WordTrace tailWord_262229 prefixEnd_262229 79792307287679858685355 := by
  unfold tailWord_262229
  simp only [CollatzResearch.WordTrace]
  refine ⟨9564277366996592992781741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6376184911331061995187827 9564277366996592992781741)
  ·
    refine ⟨3586604012623722372293153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9564277366996592992781741 3586604012623722372293153)
    ·
      refine ⟨2689953009467791779219865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3586604012623722372293153 2689953009467791779219865)
      ·
        refine ⟨2017464757100843834414899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2689953009467791779219865 2017464757100843834414899)
        ·
          refine ⟨3026197135651265751622349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2017464757100843834414899 3026197135651265751622349)
          ·
            refine ⟨1134823925869224656858381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3026197135651265751622349 1134823925869224656858381)
            ·
              refine ⟨425558972200959246321893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1134823925869224656858381 425558972200959246321893)
              ·
                refine ⟨79792307287679858685355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 425558972200959246321893 79792307287679858685355)
                ·
                  rfl

theorem cell19_262229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_262229 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262229 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262229 prefixEnd_262229 := by exact prefixLift 262229
  have htrace : WordTrace (prefixWord ++ tailWord_262229) baseStart_262229 baseEnd_262229 := by
    simpa [prefixWord, tailWord_262229, baseEnd_262229] using wordTrace_append hprefix tailTrace_262229
  have hstable : (prefixWord ++ tailWord_262229).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262229).length < 2 ^ (prefixWord ++ tailWord_262229).sum := by decide
  have hdescent : baseEnd_262229 < baseStart_262229 := by decide
  rcases family_descends (prefixWord ++ tailWord_262229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262288 : List Nat := [2, 1, 1, 1, 1, 1, 6, 6]
def baseStart_262288 : Nat := 118140960795 + 262288 * 2 ^ 59
def prefixEnd_262288 : Nat := 4983230072969 + 3 ^ 40 * 262288 * 2
def baseEnd_262288 : Nat := 79810260092785203374083

theorem tailTrace_262288 : CollatzResearch.WordTrace tailWord_262288 prefixEnd_262288 79810260092785203374083 := by
  unfold tailWord_262288
  simp only [CollatzResearch.WordTrace]
  refine ⟨4783214636891423034589759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6377619515855230712786345 4783214636891423034589759)
  ·
    refine ⟨7174821955337134551884639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4783214636891423034589759 7174821955337134551884639)
    ·
      refine ⟨10762232933005701827826959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7174821955337134551884639 10762232933005701827826959)
      ·
        refine ⟨16143349399508552741740439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10762232933005701827826959 16143349399508552741740439)
        ·
          refine ⟨24215024099262829112610659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16143349399508552741740439 24215024099262829112610659)
          ·
            refine ⟨36322536148894243668915989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24215024099262829112610659 36322536148894243668915989)
            ·
              refine ⟨1702618881979417671980437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36322536148894243668915989 1702618881979417671980437)
              ·
                refine ⟨79810260092785203374083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1702618881979417671980437 79810260092785203374083)
                ·
                  rfl

theorem cell19_262288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_262288 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262288 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262288 prefixEnd_262288 := by exact prefixLift 262288
  have htrace : WordTrace (prefixWord ++ tailWord_262288) baseStart_262288 baseEnd_262288 := by
    simpa [prefixWord, tailWord_262288, baseEnd_262288] using wordTrace_append hprefix tailTrace_262288
  have hstable : (prefixWord ++ tailWord_262288).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262288).length < 2 ^ (prefixWord ++ tailWord_262288).sum := by decide
  have hdescent : baseEnd_262288 < baseStart_262288 := by decide
  rcases family_descends (prefixWord ++ tailWord_262288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262303 : List Nat := [1, 1, 2, 6, 1, 1, 4, 3]
def baseStart_262303 : Nat := 118140960795 + 262303 * 2 ^ 59
def prefixEnd_262303 : Nat := 4983230072969 + 3 ^ 40 * 262303 * 2
def baseEnd_262303 : Nat := 79814824365269613040709

theorem tailTrace_262303 : CollatzResearch.WordTrace tailWord_262303 prefixEnd_262303 79814824365269613040709 := by
  unfold tailWord_262303
  simp only [CollatzResearch.WordTrace]
  refine ⟨9566976368728503630975563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6377984245819002420650375 9566976368728503630975563)
  ·
    refine ⟨14350464553092755446463345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9566976368728503630975563 14350464553092755446463345)
    ·
      refine ⟨10762848414819566584847509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14350464553092755446463345 10762848414819566584847509)
      ·
        refine ⟨504508519444667183664727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10762848414819566584847509 504508519444667183664727)
        ·
          refine ⟨756762779167000775497091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504508519444667183664727 756762779167000775497091)
          ·
            refine ⟨1135144168750501163245637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756762779167000775497091 1135144168750501163245637)
            ·
              refine ⟨212839531640718968108557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1135144168750501163245637 212839531640718968108557)
              ·
                refine ⟨79814824365269613040709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212839531640718968108557 79814824365269613040709)
                ·
                  rfl

theorem cell19_262303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 3].length) (baseStart_262303 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262303 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262303 prefixEnd_262303 := by exact prefixLift 262303
  have htrace : WordTrace (prefixWord ++ tailWord_262303) baseStart_262303 baseEnd_262303 := by
    simpa [prefixWord, tailWord_262303, baseEnd_262303] using wordTrace_append hprefix tailTrace_262303
  have hstable : (prefixWord ++ tailWord_262303).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262303).length < 2 ^ (prefixWord ++ tailWord_262303).sum := by decide
  have hdescent : baseEnd_262303 < baseStart_262303 := by decide
  rcases family_descends (prefixWord ++ tailWord_262303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262305 : List Nat := [1, 2, 3, 3, 1, 3, 1, 5]
def baseStart_262305 : Nat := 118140960795 + 262305 * 2 ^ 59
def prefixEnd_262305 : Nat := 4983230072969 + 3 ^ 40 * 262305 * 2
def baseEnd_262305 : Nat := 79815432934934200996259

theorem tailTrace_262305 : CollatzResearch.WordTrace tailWord_262305 prefixEnd_262305 79815432934934200996259 := by
  unfold tailWord_262305
  simp only [CollatzResearch.WordTrace]
  refine ⟨9567049314721257972548369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6378032876480838648365579 9567049314721257972548369)
  ·
    refine ⟨7175286986040943479411277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9567049314721257972548369 7175286986040943479411277)
    ·
      refine ⟨2690732619765353804779229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7175286986040943479411277 2690732619765353804779229)
      ·
        refine ⟨1009024732412007676792211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2690732619765353804779229 1009024732412007676792211)
        ·
          refine ⟨1513537098618011515188317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009024732412007676792211 1513537098618011515188317)
          ·
            refine ⟨567576411981754318195619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1513537098618011515188317 567576411981754318195619)
            ·
              refine ⟨851364617972631477293429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567576411981754318195619 851364617972631477293429)
              ·
                refine ⟨79815432934934200996259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 851364617972631477293429 79815432934934200996259)
                ·
                  rfl

theorem cell19_262305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_262305 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262305 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262305 prefixEnd_262305 := by exact prefixLift 262305
  have htrace : WordTrace (prefixWord ++ tailWord_262305) baseStart_262305 baseEnd_262305 := by
    simpa [prefixWord, tailWord_262305, baseEnd_262305] using wordTrace_append hprefix tailTrace_262305
  have hstable : (prefixWord ++ tailWord_262305).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262305).length < 2 ^ (prefixWord ++ tailWord_262305).sum := by decide
  have hdescent : baseEnd_262305 < baseStart_262305 := by decide
  rcases family_descends (prefixWord ++ tailWord_262305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262318 : List Nat := [4, 1, 4, 2, 2, 1, 5]
def baseStart_262318 : Nat := 118140960795 + 262318 * 2 ^ 59
def prefixEnd_262318 : Nat := 4983230072969 + 3 ^ 40 * 262318 * 2
def baseEnd_262318 : Nat := 26606462879251340902445

theorem tailTrace_262318 : CollatzResearch.WordTrace tailWord_262318 prefixEnd_262318 26606462879251340902445 := by
  unfold tailWord_262318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1195940432959270149096451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6378348975782774128514405 1195940432959270149096451)
  ·
    refine ⟨1793910649438905223644677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1195940432959270149096451 1793910649438905223644677)
    ·
      refine ⟨336358246769794729433377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1793910649438905223644677 336358246769794729433377)
      ·
        refine ⟨252268685077346047075033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336358246769794729433377 252268685077346047075033)
        ·
          refine ⟨189201513808009535306275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252268685077346047075033 189201513808009535306275)
          ·
            refine ⟨283802270712014302959413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189201513808009535306275 283802270712014302959413)
            ·
              refine ⟨26606462879251340902445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 283802270712014302959413 26606462879251340902445)
              ·
                rfl

theorem cell19_262318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 5].length) (baseStart_262318 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262318 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262318 prefixEnd_262318 := by exact prefixLift 262318
  have htrace : WordTrace (prefixWord ++ tailWord_262318) baseStart_262318 baseEnd_262318 := by
    simpa [prefixWord, tailWord_262318, baseEnd_262318] using wordTrace_append hprefix tailTrace_262318
  have hstable : (prefixWord ++ tailWord_262318).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262318).length < 2 ^ (prefixWord ++ tailWord_262318).sum := by decide
  have hdescent : baseEnd_262318 < baseStart_262318 := by decide
  rcases family_descends (prefixWord ++ tailWord_262318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262381 : List Nat := [1, 5, 1, 2, 3, 7]
def baseStart_262381 : Nat := 118140960795 + 262381 * 2 ^ 59
def prefixEnd_262381 : Nat := 4983230072969 + 3 ^ 40 * 262381 * 2
def baseEnd_262381 : Nat := 8870950953576504811907

theorem tailTrace_262381 : CollatzResearch.WordTrace tailWord_262381 prefixEnd_262381 8870950953576504811907 := by
  unfold tailWord_262381
  simp only [CollatzResearch.WordTrace]
  refine ⟨9569821262445922952314997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6379880841630615301543331 9569821262445922952314997)
  ·
    refine ⟨897170743354305276779531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9569821262445922952314997 897170743354305276779531)
    ·
      refine ⟨1345756115031457915169297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 897170743354305276779531 1345756115031457915169297)
      ·
        refine ⟨1009317086273593436376973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1345756115031457915169297 1009317086273593436376973)
        ·
          refine ⟨378493907352597538641365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1009317086273593436376973 378493907352597538641365)
          ·
            refine ⟨8870950953576504811907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 378493907352597538641365 8870950953576504811907)
            ·
              rfl

theorem cell19_262381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 7].length) (baseStart_262381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262381 prefixEnd_262381 := by exact prefixLift 262381
  have htrace : WordTrace (prefixWord ++ tailWord_262381) baseStart_262381 baseEnd_262381 := by
    simpa [prefixWord, tailWord_262381, baseEnd_262381] using wordTrace_append hprefix tailTrace_262381
  have hstable : (prefixWord ++ tailWord_262381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262381).length < 2 ^ (prefixWord ++ tailWord_262381).sum := by decide
  have hdescent : baseEnd_262381 < baseStart_262381 := by decide
  rcases family_descends (prefixWord ++ tailWord_262381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262383 : List Nat := [1, 1, 2, 1, 6, 8]
def baseStart_262383 : Nat := 118140960795 + 262383 * 2 ^ 59
def prefixEnd_262383 : Nat := 4983230072969 + 3 ^ 40 * 262383 * 2
def baseEnd_262383 : Nat := 8871018572428125695857

theorem tailTrace_262383 : CollatzResearch.WordTrace tailWord_262383 prefixEnd_262383 8871018572428125695857 := by
  unfold tailWord_262383
  simp only [CollatzResearch.WordTrace]
  refine ⟨9569894208438677293887803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6379929472292451529258535 9569894208438677293887803)
  ·
    refine ⟨14354841312658015940831705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9569894208438677293887803 14354841312658015940831705)
    ·
      refine ⟨10766130984493511955623779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14354841312658015940831705 10766130984493511955623779)
      ·
        refine ⟨16149196476740267933435669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10766130984493511955623779 16149196476740267933435669)
        ·
          refine ⟨756993584847200059379797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16149196476740267933435669 756993584847200059379797)
          ·
            refine ⟨8871018572428125695857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 756993584847200059379797 8871018572428125695857)
            ·
              rfl

theorem cell19_262383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 8].length) (baseStart_262383 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262383 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262383 prefixEnd_262383 := by exact prefixLift 262383
  have htrace : WordTrace (prefixWord ++ tailWord_262383) baseStart_262383 baseEnd_262383 := by
    simpa [prefixWord, tailWord_262383, baseEnd_262383] using wordTrace_append hprefix tailTrace_262383
  have hstable : (prefixWord ++ tailWord_262383).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262383).length < 2 ^ (prefixWord ++ tailWord_262383).sum := by decide
  have hdescent : baseEnd_262383 < baseStart_262383 := by decide
  rcases family_descends (prefixWord ++ tailWord_262383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262421 : List Nat := [1, 3, 2, 1, 2, 1, 2, 7]
def baseStart_262421 : Nat := 118140960795 + 262421 * 2 ^ 59
def prefixEnd_262421 : Nat := 4983230072969 + 3 ^ 40 * 262421 * 2
def baseEnd_262421 : Nat := 79850729975480302418165

theorem tailTrace_262421 : CollatzResearch.WordTrace tailWord_262421 prefixEnd_262421 79850729975480302418165 := by
  unfold tailWord_262421
  simp only [CollatzResearch.WordTrace]
  refine ⟨9571280182301009783771117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6380853454867339855847411 9571280182301009783771117)
  ·
    refine ⟨3589230068362878668914169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9571280182301009783771117 3589230068362878668914169)
    ·
      refine ⟨2691922551272159001685627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3589230068362878668914169 2691922551272159001685627)
      ·
        refine ⟨4037883826908238502528441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2691922551272159001685627 4037883826908238502528441)
        ·
          refine ⟨3028412870181178876896331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4037883826908238502528441 3028412870181178876896331)
          ·
            refine ⟨4542619305271768315344497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3028412870181178876896331 4542619305271768315344497)
            ·
              refine ⟨3406964478953826236508373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4542619305271768315344497 3406964478953826236508373)
              ·
                refine ⟨79850729975480302418165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3406964478953826236508373 79850729975480302418165)
                ·
                  rfl

theorem cell19_262421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_262421 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262421 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262421 prefixEnd_262421 := by exact prefixLift 262421
  have htrace : WordTrace (prefixWord ++ tailWord_262421) baseStart_262421 baseEnd_262421 := by
    simpa [prefixWord, tailWord_262421, baseEnd_262421] using wordTrace_append hprefix tailTrace_262421
  have hstable : (prefixWord ++ tailWord_262421).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262421).length < 2 ^ (prefixWord ++ tailWord_262421).sum := by decide
  have hdescent : baseEnd_262421 < baseStart_262421 := by decide
  rcases family_descends (prefixWord ++ tailWord_262421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262514 : List Nat := [3, 2, 1, 2, 1, 4, 2, 4]
def baseStart_262514 : Nat := 118140960795 + 262514 * 2 ^ 59
def prefixEnd_262514 : Nat := 4983230072969 + 3 ^ 40 * 262514 * 2
def baseEnd_262514 : Nat := 79879028464883642351245

theorem tailTrace_262514 : CollatzResearch.WordTrace tailWord_262514 prefixEnd_262514 79879028464883642351245 := by
  unfold tailWord_262514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2393668042741021666726649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6383114780642724444604397 2393668042741021666726649)
  ·
    refine ⟨1795251032055766250044987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2393668042741021666726649 1795251032055766250044987)
    ·
      refine ⟨2692876548083649375067481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1795251032055766250044987 2692876548083649375067481)
      ·
        refine ⟨2019657411062737031300611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2692876548083649375067481 2019657411062737031300611)
        ·
          refine ⟨3029486116594105546950917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2019657411062737031300611 3029486116594105546950917)
          ·
            refine ⟨568028646861394790053297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3029486116594105546950917 568028646861394790053297)
            ·
              refine ⟨426021485146046092539973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568028646861394790053297 426021485146046092539973)
              ·
                refine ⟨79879028464883642351245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 426021485146046092539973 79879028464883642351245)
                ·
                  rfl

theorem cell19_262514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_262514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262514 prefixEnd_262514 := by exact prefixLift 262514
  have htrace : WordTrace (prefixWord ++ tailWord_262514) baseStart_262514 baseEnd_262514 := by
    simpa [prefixWord, tailWord_262514, baseEnd_262514] using wordTrace_append hprefix tailTrace_262514
  have hstable : (prefixWord ++ tailWord_262514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262514).length < 2 ^ (prefixWord ++ tailWord_262514).sum := by decide
  have hdescent : baseEnd_262514 < baseStart_262514 := by decide
  rcases family_descends (prefixWord ++ tailWord_262514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262535 : List Nat := [1, 1, 4, 2, 2, 1, 1, 7]
def baseStart_262535 : Nat := 118140960795 + 262535 * 2 ^ 59
def prefixEnd_262535 : Nat := 4983230072969 + 3 ^ 40 * 262535 * 2
def baseEnd_262535 : Nat := 79885418446361815884521

theorem tailTrace_262535 : CollatzResearch.WordTrace tailWord_262535 prefixEnd_262535 79885418446361815884521 := by
  unfold tailWord_262535
  simp only [CollatzResearch.WordTrace]
  refine ⟨9575438103888007253421059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6383625402592004835614039 9575438103888007253421059)
  ·
    refine ⟨14363157155832010880131589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9575438103888007253421059 14363157155832010880131589)
    ·
      refine ⟨2693091966718502040024673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14363157155832010880131589 2693091966718502040024673)
      ·
        refine ⟨2019818975038876530018505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2693091966718502040024673 2019818975038876530018505)
        ·
          refine ⟨1514864231279157397513879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2019818975038876530018505 1514864231279157397513879)
          ·
            refine ⟨2272296346918736096270819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514864231279157397513879 2272296346918736096270819)
            ·
              refine ⟨3408444520378104144406229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2272296346918736096270819 3408444520378104144406229)
              ·
                refine ⟨79885418446361815884521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3408444520378104144406229 79885418446361815884521)
                ·
                  rfl

theorem cell19_262535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_262535 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262535 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262535 prefixEnd_262535 := by exact prefixLift 262535
  have htrace : WordTrace (prefixWord ++ tailWord_262535) baseStart_262535 baseEnd_262535 := by
    simpa [prefixWord, tailWord_262535, baseEnd_262535] using wordTrace_append hprefix tailTrace_262535
  have hstable : (prefixWord ++ tailWord_262535).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262535).length < 2 ^ (prefixWord ++ tailWord_262535).sum := by decide
  have hdescent : baseEnd_262535 < baseStart_262535 := by decide
  rcases family_descends (prefixWord ++ tailWord_262535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262554 : List Nat := [3, 1, 1, 4, 1, 9]
def baseStart_262554 : Nat := 118140960795 + 262554 * 2 ^ 59
def prefixEnd_262554 : Nat := 4983230072969 + 3 ^ 40 * 262554 * 2
def baseEnd_262554 : Nat := 8876799984241711273583

theorem tailTrace_262554 : CollatzResearch.WordTrace tailWord_262554 prefixEnd_262554 8876799984241711273583 := by
  unfold tailWord_262554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2394032772704793374590679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6384087393879448998908477 2394032772704793374590679)
  ·
    refine ⟨3591049159057190061886019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2394032772704793374590679 3591049159057190061886019)
    ·
      refine ⟨5386573738585785092829029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3591049159057190061886019 5386573738585785092829029)
      ·
        refine ⟨1009982575984834704905443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5386573738585785092829029 1009982575984834704905443)
        ·
          refine ⟨1514973863977252057358165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009982575984834704905443 1514973863977252057358165)
          ·
            refine ⟨8876799984241711273583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1514973863977252057358165 8876799984241711273583)
            ·
              rfl

theorem cell19_262554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 9].length) (baseStart_262554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262554 prefixEnd_262554 := by exact prefixLift 262554
  have htrace : WordTrace (prefixWord ++ tailWord_262554) baseStart_262554 baseEnd_262554 := by
    simpa [prefixWord, tailWord_262554, baseEnd_262554] using wordTrace_append hprefix tailTrace_262554
  have hstable : (prefixWord ++ tailWord_262554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262554).length < 2 ^ (prefixWord ++ tailWord_262554).sum := by decide
  have hdescent : baseEnd_262554 < baseStart_262554 := by decide
  rcases family_descends (prefixWord ++ tailWord_262554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262588 : List Nat := [2, 2, 2, 4, 1, 2, 3, 3]
def baseStart_262588 : Nat := 118140960795 + 262588 * 2 ^ 59
def prefixEnd_262588 : Nat := 4983230072969 + 3 ^ 40 * 262588 * 2
def baseEnd_262588 : Nat := 79901545542473396706599

theorem tailTrace_262588 : CollatzResearch.WordTrace tailWord_262588 prefixEnd_262588 79901545542473396706599 := by
  unfold tailWord_262588
  simp only [CollatzResearch.WordTrace]
  refine ⟨4788685586347998652550209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6384914115130664870066945 4788685586347998652550209)
  ·
    refine ⟨3591514189760998989412657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4788685586347998652550209 3591514189760998989412657)
    ·
      refine ⟨2693635642320749242059493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3591514189760998989412657 2693635642320749242059493)
      ·
        refine ⟨505056682935140482886155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2693635642320749242059493 505056682935140482886155)
        ·
          refine ⟨757585024402710724329233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505056682935140482886155 757585024402710724329233)
          ·
            refine ⟨568188768302033043246925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 757585024402710724329233 568188768302033043246925)
            ·
              refine ⟨213070788113262391217597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 568188768302033043246925 213070788113262391217597)
              ·
                refine ⟨79901545542473396706599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213070788113262391217597 79901545542473396706599)
                ·
                  rfl

theorem cell19_262588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_262588 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262588 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262588 prefixEnd_262588 := by exact prefixLift 262588
  have htrace : WordTrace (prefixWord ++ tailWord_262588) baseStart_262588 baseEnd_262588 := by
    simpa [prefixWord, tailWord_262588, baseEnd_262588] using wordTrace_append hprefix tailTrace_262588
  have hstable : (prefixWord ++ tailWord_262588).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262588).length < 2 ^ (prefixWord ++ tailWord_262588).sum := by decide
  have hdescent : baseEnd_262588 < baseStart_262588 := by decide
  rcases family_descends (prefixWord ++ tailWord_262588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262645 : List Nat := [1, 3, 5, 1, 2, 1, 1, 5]
def baseStart_262645 : Nat := 118140960795 + 262645 * 2 ^ 59
def prefixEnd_262645 : Nat := 4983230072969 + 3 ^ 40 * 262645 * 2
def baseEnd_262645 : Nat := 79918889777914153439777

theorem tailTrace_262645 : CollatzResearch.WordTrace tailWord_262645 prefixEnd_262645 79918889777914153439777 := by
  unfold tailWord_262645
  simp only [CollatzResearch.WordTrace]
  refine ⟨9579450133489496039925389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6386300088992997359950259 9579450133489496039925389)
  ·
    refine ⟨3592293800058561014972021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9579450133489496039925389 3592293800058561014972021)
    ·
      refine ⟨336777543755490095153627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3592293800058561014972021 336777543755490095153627)
      ·
        refine ⟨505166315633235142730441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336777543755490095153627 505166315633235142730441)
        ·
          refine ⟨378874736724926357047831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505166315633235142730441 378874736724926357047831)
          ·
            refine ⟨568312105087389535571747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378874736724926357047831 568312105087389535571747)
            ·
              refine ⟨852468157631084303357621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568312105087389535571747 852468157631084303357621)
              ·
                refine ⟨79918889777914153439777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 852468157631084303357621 79918889777914153439777)
                ·
                  rfl

theorem cell19_262645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 5].length) (baseStart_262645 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262645 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262645 prefixEnd_262645 := by exact prefixLift 262645
  have htrace : WordTrace (prefixWord ++ tailWord_262645) baseStart_262645 baseEnd_262645 := by
    simpa [prefixWord, tailWord_262645, baseEnd_262645] using wordTrace_append hprefix tailTrace_262645
  have hstable : (prefixWord ++ tailWord_262645).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262645).length < 2 ^ (prefixWord ++ tailWord_262645).sum := by decide
  have hdescent : baseEnd_262645 < baseStart_262645 := by decide
  rcases family_descends (prefixWord ++ tailWord_262645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262662 : List Nat := [6, 2, 1, 1, 1, 1, 7]
def baseStart_262662 : Nat := 118140960795 + 262662 * 2 ^ 59
def prefixEnd_262662 : Nat := 4983230072969 + 3 ^ 40 * 262662 * 2
def baseEnd_262662 : Nat := 26641354206687717020651

theorem tailTrace_262662 : CollatzResearch.WordTrace tailWord_262662 prefixEnd_262662 26641354206687717020651 := by
  unfold tailWord_262662
  simp only [CollatzResearch.WordTrace]
  refine ⟨299377192950872123227945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6386713449618605295529493 299377192950872123227945)
  ·
    refine ⟨224532894713154092420959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299377192950872123227945 224532894713154092420959)
    ·
      refine ⟨336799342069731138631439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224532894713154092420959 336799342069731138631439)
      ·
        refine ⟨505199013104596707947159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336799342069731138631439 505199013104596707947159)
        ·
          refine ⟨757798519656895061920739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505199013104596707947159 757798519656895061920739)
          ·
            refine ⟨1136697779485342592881109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757798519656895061920739 1136697779485342592881109)
            ·
              refine ⟨26641354206687717020651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1136697779485342592881109 26641354206687717020651)
              ·
                rfl

theorem cell19_262662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 7].length) (baseStart_262662 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262662 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262662 prefixEnd_262662 := by exact prefixLift 262662
  have htrace : WordTrace (prefixWord ++ tailWord_262662) baseStart_262662 baseEnd_262662 := by
    simpa [prefixWord, tailWord_262662, baseEnd_262662] using wordTrace_append hprefix tailTrace_262662
  have hstable : (prefixWord ++ tailWord_262662).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262662).length < 2 ^ (prefixWord ++ tailWord_262662).sum := by decide
  have hdescent : baseEnd_262662 < baseStart_262662 := by decide
  rcases family_descends (prefixWord ++ tailWord_262662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262668 : List Nat := [2, 2, 1, 2, 4, 1, 7]
def baseStart_262668 : Nat := 118140960795 + 262668 * 2 ^ 59
def prefixEnd_262668 : Nat := 4983230072969 + 3 ^ 40 * 262668 * 2
def baseEnd_262668 : Nat := 26641962776352304976201

theorem tailTrace_262668 : CollatzResearch.WordTrace tailWord_262668 prefixEnd_262668 26641962776352304976201 := by
  unfold tailWord_262668
  simp only [CollatzResearch.WordTrace]
  refine ⟨4790144506203085484006329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6386859341604113978675105 4790144506203085484006329)
  ·
    refine ⟨3592608379652314113004747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4790144506203085484006329 3592608379652314113004747)
    ·
      refine ⟨5388912569478471169507121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3592608379652314113004747 5388912569478471169507121)
      ·
        refine ⟨4041684427108853377130341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5388912569478471169507121 4041684427108853377130341)
        ·
          refine ⟨757815830082910008211939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4041684427108853377130341 757815830082910008211939)
          ·
            refine ⟨1136723745124365012317909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757815830082910008211939 1136723745124365012317909)
            ·
              refine ⟨26641962776352304976201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1136723745124365012317909 26641962776352304976201)
              ·
                rfl

theorem cell19_262668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 7].length) (baseStart_262668 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262668 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262668 prefixEnd_262668 := by exact prefixLift 262668
  have htrace : WordTrace (prefixWord ++ tailWord_262668) baseStart_262668 baseEnd_262668 := by
    simpa [prefixWord, tailWord_262668, baseEnd_262668] using wordTrace_append hprefix tailTrace_262668
  have hstable : (prefixWord ++ tailWord_262668).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262668).length < 2 ^ (prefixWord ++ tailWord_262668).sum := by decide
  have hdescent : baseEnd_262668 < baseStart_262668 := by decide
  rcases family_descends (prefixWord ++ tailWord_262668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262685 : List Nat := [1, 4, 2, 2, 1, 3, 2, 4]
def baseStart_262685 : Nat := 118140960795 + 262685 * 2 ^ 59
def prefixEnd_262685 : Nat := 4983230072969 + 3 ^ 40 * 262685 * 2
def baseEnd_262685 : Nat := 79931061171205912550779

theorem tailTrace_262685 : CollatzResearch.WordTrace tailWord_262685 prefixEnd_262685 79931061171205912550779 := by
  unfold tailWord_262685
  simp only [CollatzResearch.WordTrace]
  refine ⟨9580909053344582871381509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6387272702229721914254339 9580909053344582871381509)
  ·
    refine ⟨1796420447502109288384033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9580909053344582871381509 1796420447502109288384033)
    ·
      refine ⟨1347315335626581966288025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1796420447502109288384033 1347315335626581966288025)
      ·
        refine ⟨1010486501719936474716019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1347315335626581966288025 1010486501719936474716019)
        ·
          refine ⟨1515729752579904712074029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010486501719936474716019 1515729752579904712074029)
          ·
            refine ⟨568398657217464267027761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1515729752579904712074029 568398657217464267027761)
            ·
              refine ⟨426298992913098200270821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568398657217464267027761 426298992913098200270821)
              ·
                refine ⟨79931061171205912550779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 426298992913098200270821 79931061171205912550779)
                ·
                  rfl

theorem cell19_262685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_262685 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262685 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262685 prefixEnd_262685 := by exact prefixLift 262685
  have htrace : WordTrace (prefixWord ++ tailWord_262685) baseStart_262685 baseEnd_262685 := by
    simpa [prefixWord, tailWord_262685, baseEnd_262685] using wordTrace_append hprefix tailTrace_262685
  have hstable : (prefixWord ++ tailWord_262685).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262685).length < 2 ^ (prefixWord ++ tailWord_262685).sum := by decide
  have hdescent : baseEnd_262685 < baseStart_262685 := by decide
  rcases family_descends (prefixWord ++ tailWord_262685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262706 : List Nat := [3, 2, 1, 1, 2, 1, 4, 5]
def baseStart_262706 : Nat := 118140960795 + 262706 * 2 ^ 59
def prefixEnd_262706 : Nat := 4983230072969 + 3 ^ 40 * 262706 * 2
def baseEnd_262706 : Nat := 79937451152684086084055

theorem tailTrace_262706 : CollatzResearch.WordTrace tailWord_262706 prefixEnd_262706 79937451152684086084055 := by
  unfold tailWord_262706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2395418746567125864473993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6387783324179002305263981 2395418746567125864473993)
  ·
    refine ⟨1796564059925344398355495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2395418746567125864473993 1796564059925344398355495)
    ·
      refine ⟨2694846089888016597533243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1796564059925344398355495 2694846089888016597533243)
      ·
        refine ⟨4042269134832024896299865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2694846089888016597533243 4042269134832024896299865)
        ·
          refine ⟨3031701851124018672224899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4042269134832024896299865 3031701851124018672224899)
          ·
            refine ⟨4547552776686028008337349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3031701851124018672224899 4547552776686028008337349)
            ·
              refine ⟨852666145628630251563253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4547552776686028008337349 852666145628630251563253)
              ·
                refine ⟨79937451152684086084055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 852666145628630251563253 79937451152684086084055)
                ·
                  rfl

theorem cell19_262706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_262706 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262706 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262706 prefixEnd_262706 := by exact prefixLift 262706
  have htrace : WordTrace (prefixWord ++ tailWord_262706) baseStart_262706 baseEnd_262706 := by
    simpa [prefixWord, tailWord_262706, baseEnd_262706] using wordTrace_append hprefix tailTrace_262706
  have hstable : (prefixWord ++ tailWord_262706).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262706).length < 2 ^ (prefixWord ++ tailWord_262706).sum := by decide
  have hdescent : baseEnd_262706 < baseStart_262706 := by decide
  rcases family_descends (prefixWord ++ tailWord_262706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262744 : List Nat := [2, 1, 2, 2, 1, 2, 5, 4]
def baseStart_262744 : Nat := 118140960795 + 262744 * 2 ^ 59
def prefixEnd_262744 : Nat := 4983230072969 + 3 ^ 40 * 262744 * 2
def baseEnd_262744 : Nat := 79949013976311257239507

theorem tailTrace_262744 : CollatzResearch.WordTrace tailWord_262744 prefixEnd_262744 79949013976311257239507 := by
  unfold tailWord_262744
  simp only [CollatzResearch.WordTrace]
  refine ⟨4791530480065417973889643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6388707306753890631852857 4791530480065417973889643)
  ·
    refine ⟨7187295720098126960834465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4791530480065417973889643 7187295720098126960834465)
    ·
      refine ⟨5390471790073595220625849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7187295720098126960834465 5390471790073595220625849)
      ·
        refine ⟨4042853842555196415469387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5390471790073595220625849 4042853842555196415469387)
        ·
          refine ⟨6064280763832794623204081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4042853842555196415469387 6064280763832794623204081)
          ·
            refine ⟨4548210572874595967403061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6064280763832794623204081 4548210572874595967403061)
            ·
              refine ⟨426394741206993371944037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4548210572874595967403061 426394741206993371944037)
              ·
                refine ⟨79949013976311257239507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 426394741206993371944037 79949013976311257239507)
                ·
                  rfl

theorem cell19_262744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_262744 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262744 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262744 prefixEnd_262744 := by exact prefixLift 262744
  have htrace : WordTrace (prefixWord ++ tailWord_262744) baseStart_262744 baseEnd_262744 := by
    simpa [prefixWord, tailWord_262744, baseEnd_262744] using wordTrace_append hprefix tailTrace_262744
  have hstable : (prefixWord ++ tailWord_262744).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262744).length < 2 ^ (prefixWord ++ tailWord_262744).sum := by decide
  have hdescent : baseEnd_262744 < baseStart_262744 := by decide
  rcases family_descends (prefixWord ++ tailWord_262744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262816 : List Nat := [2, 1, 1, 4, 4, 2, 2, 3]
def baseStart_262816 : Nat := 118140960795 + 262816 * 2 ^ 59
def prefixEnd_262816 : Nat := 4983230072969 + 3 ^ 40 * 262816 * 2
def baseEnd_262816 : Nat := 79970922484236423639311

theorem tailTrace_262816 : CollatzResearch.WordTrace tailWord_262816 prefixEnd_262816 79970922484236423639311 := by
  unfold tailWord_262816
  simp only [CollatzResearch.WordTrace]
  refine ⟨4792843507934996122200151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6390458010579994829600201 4792843507934996122200151)
  ·
    refine ⟨7189265261902494183300227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4792843507934996122200151 7189265261902494183300227)
    ·
      refine ⟨10783897892853741274950341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7189265261902494183300227 10783897892853741274950341)
      ·
        refine ⟨2021980854910076489053189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10783897892853741274950341 2021980854910076489053189)
        ·
          refine ⟨379121410295639341697473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2021980854910076489053189 379121410295639341697473)
          ·
            refine ⟨284341057721729506273105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379121410295639341697473 284341057721729506273105)
            ·
              refine ⟨213255793291297129704829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284341057721729506273105 213255793291297129704829)
              ·
                refine ⟨79970922484236423639311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213255793291297129704829 79970922484236423639311)
                ·
                  rfl

theorem cell19_262816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_262816 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262816 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262816 prefixEnd_262816 := by exact prefixLift 262816
  have htrace : WordTrace (prefixWord ++ tailWord_262816) baseStart_262816 baseEnd_262816 := by
    simpa [prefixWord, tailWord_262816, baseEnd_262816] using wordTrace_append hprefix tailTrace_262816
  have hstable : (prefixWord ++ tailWord_262816).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262816).length < 2 ^ (prefixWord ++ tailWord_262816).sum := by decide
  have hdescent : baseEnd_262816 < baseStart_262816 := by decide
  rcases family_descends (prefixWord ++ tailWord_262816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262820 : List Nat := [2, 3, 1, 2, 2, 1, 3, 5]
def baseStart_262820 : Nat := 118140960795 + 262820 * 2 ^ 59
def prefixEnd_262820 : Nat := 4983230072969 + 3 ^ 40 * 262820 * 2
def baseEnd_262820 : Nat := 79972139623565599550411

theorem tailTrace_262820 : CollatzResearch.WordTrace tailWord_262820 prefixEnd_262820 79972139623565599550411 := by
  unfold tailWord_262820
  simp only [CollatzResearch.WordTrace]
  refine ⟨4792916453927750463772957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6390555271903667285030609 4792916453927750463772957)
  ·
    refine ⟨1797343670222906423914859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4792916453927750463772957 1797343670222906423914859)
    ·
      refine ⟨2696015505334359635872289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1797343670222906423914859 2696015505334359635872289)
      ·
        refine ⟨2022011629000769726904217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2696015505334359635872289 2022011629000769726904217)
        ·
          refine ⟨1516508721750577295178163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2022011629000769726904217 1516508721750577295178163)
          ·
            refine ⟨2274763082625865942767245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1516508721750577295178163 2274763082625865942767245)
            ·
              refine ⟨853036155984699728537717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2274763082625865942767245 853036155984699728537717)
              ·
                refine ⟨79972139623565599550411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 853036155984699728537717 79972139623565599550411)
                ·
                  rfl

theorem cell19_262820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_262820 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262820 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262820 prefixEnd_262820 := by exact prefixLift 262820
  have htrace : WordTrace (prefixWord ++ tailWord_262820) baseStart_262820 baseEnd_262820 := by
    simpa [prefixWord, tailWord_262820, baseEnd_262820] using wordTrace_append hprefix tailTrace_262820
  have hstable : (prefixWord ++ tailWord_262820).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262820).length < 2 ^ (prefixWord ++ tailWord_262820).sum := by decide
  have hdescent : baseEnd_262820 < baseStart_262820 := by decide
  rcases family_descends (prefixWord ++ tailWord_262820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262837 : List Nat := [1, 3, 3, 3, 1, 3, 5]
def baseStart_262837 : Nat := 118140960795 + 262837 * 2 ^ 59
def prefixEnd_262837 : Nat := 4983230072969 + 3 ^ 40 * 262837 * 2
def baseEnd_262837 : Nat := 26659104155238199057529

theorem tailTrace_262837 : CollatzResearch.WordTrace tailWord_262837 prefixEnd_262837 26659104155238199057529 := by
  unfold tailWord_262837
  simp only [CollatzResearch.WordTrace]
  refine ⟨9586452948793912830914765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6390968632529275220609843 9586452948793912830914765)
  ·
    refine ⟨3594919855797717311593037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9586452948793912830914765 3594919855797717311593037)
    ·
      refine ⟨1348094945924143991847389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3594919855797717311593037 1348094945924143991847389)
      ·
        refine ⟨505535604721553996942771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1348094945924143991847389 505535604721553996942771)
        ·
          refine ⟨758303407082330995414157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505535604721553996942771 758303407082330995414157)
          ·
            refine ⟨284363777655874123280309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 758303407082330995414157 284363777655874123280309)
            ·
              refine ⟨26659104155238199057529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284363777655874123280309 26659104155238199057529)
              ·
                rfl

theorem cell19_262837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 5].length) (baseStart_262837 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262837 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262837 prefixEnd_262837 := by exact prefixLift 262837
  have htrace : WordTrace (prefixWord ++ tailWord_262837) baseStart_262837 baseEnd_262837 := by
    simpa [prefixWord, tailWord_262837, baseEnd_262837] using wordTrace_append hprefix tailTrace_262837
  have hstable : (prefixWord ++ tailWord_262837).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262837).length < 2 ^ (prefixWord ++ tailWord_262837).sum := by decide
  have hdescent : baseEnd_262837 < baseStart_262837 := by decide
  rcases family_descends (prefixWord ++ tailWord_262837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262858 : List Nat := [3, 1, 2, 1, 4, 1, 1, 6]
def baseStart_262858 : Nat := 118140960795 + 262858 * 2 ^ 59
def prefixEnd_262858 : Nat := 4983230072969 + 3 ^ 40 * 262858 * 2
def baseEnd_262858 : Nat := 79983702447192770705863

theorem tailTrace_262858 : CollatzResearch.WordTrace tailWord_262858 prefixEnd_262858 79983702447192770705863 := by
  unfold tailWord_262858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2396804720429458354357307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6391479254478555611619485 2396804720429458354357307)
  ·
    refine ⟨3595207080644187531535961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2396804720429458354357307 3595207080644187531535961)
    ·
      refine ⟨2696405310483140648651971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3595207080644187531535961 2696405310483140648651971)
      ·
        refine ⟨4044607965724710972977957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2696405310483140648651971 4044607965724710972977957)
        ·
          refine ⟨758363993573383307433367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4044607965724710972977957 758363993573383307433367)
          ·
            refine ⟨1137545990360074961150051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758363993573383307433367 1137545990360074961150051)
            ·
              refine ⟨1706318985540112441725077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137545990360074961150051 1706318985540112441725077)
              ·
                refine ⟨79983702447192770705863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1706318985540112441725077 79983702447192770705863)
                ·
                  rfl

theorem cell19_262858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_262858 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_262858 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_262858 prefixEnd_262858 := by exact prefixLift 262858
  have htrace : WordTrace (prefixWord ++ tailWord_262858) baseStart_262858 baseEnd_262858 := by
    simpa [prefixWord, tailWord_262858, baseEnd_262858] using wordTrace_append hprefix tailTrace_262858
  have hstable : (prefixWord ++ tailWord_262858).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262858).length < 2 ^ (prefixWord ++ tailWord_262858).sum := by decide
  have hdescent : baseEnd_262858 < baseStart_262858 := by decide
  rcases family_descends (prefixWord ++ tailWord_262858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263029 : List Nat := [1, 3, 4, 1, 1, 2, 1, 6]
def baseStart_263029 : Nat := 118140960795 + 263029 * 2 ^ 59
def prefixEnd_263029 : Nat := 4983230072969 + 3 ^ 40 * 263029 * 2
def baseEnd_263029 : Nat := 80035735153515040905397

theorem tailTrace_263029 : CollatzResearch.WordTrace tailWord_263029 prefixEnd_263029 80035735153515040905397 := by
  unfold tailWord_263029
  simp only [CollatzResearch.WordTrace]
  refine ⟨9593455764098329621904141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6395637176065553081269427 9593455764098329621904141)
  ·
    refine ⟨3597545911536873608214053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9593455764098329621904141 3597545911536873608214053)
    ·
      refine ⟨674539858413163801540135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3597545911536873608214053 674539858413163801540135)
      ·
        refine ⟨1011809787619745702310203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674539858413163801540135 1011809787619745702310203)
        ·
          refine ⟨1517714681429618553465305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011809787619745702310203 1517714681429618553465305)
          ·
            refine ⟨1138286011072213915098979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1517714681429618553465305 1138286011072213915098979)
            ·
              refine ⟨1707429016608320872648469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138286011072213915098979 1707429016608320872648469)
              ·
                refine ⟨80035735153515040905397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1707429016608320872648469 80035735153515040905397)
                ·
                  rfl

theorem cell19_263029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_263029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263029 prefixEnd_263029 := by exact prefixLift 263029
  have htrace : WordTrace (prefixWord ++ tailWord_263029) baseStart_263029 baseEnd_263029 := by
    simpa [prefixWord, tailWord_263029, baseEnd_263029] using wordTrace_append hprefix tailTrace_263029
  have hstable : (prefixWord ++ tailWord_263029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263029).length < 2 ^ (prefixWord ++ tailWord_263029).sum := by decide
  have hdescent : baseEnd_263029 < baseStart_263029 := by decide
  rcases family_descends (prefixWord ++ tailWord_263029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263048 : List Nat := [2, 1, 3, 3, 2, 1, 2, 5]
def baseStart_263048 : Nat := 118140960795 + 263048 * 2 ^ 59
def prefixEnd_263048 : Nat := 4983230072969 + 3 ^ 40 * 263048 * 2
def baseEnd_263048 : Nat := 80041516565328626483123

theorem tailTrace_263048 : CollatzResearch.WordTrace tailWord_263048 prefixEnd_263048 80041516565328626483123 := by
  unfold tailWord_263048
  simp only [CollatzResearch.WordTrace]
  refine ⟨4797074375514747933422899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6396099167352997244563865 4797074375514747933422899)
  ·
    refine ⟨7195611563272121900134349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4797074375514747933422899 7195611563272121900134349)
    ·
      refine ⟨2698354336227045712550381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7195611563272121900134349 2698354336227045712550381)
      ·
        refine ⟨1011882876085142142206393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2698354336227045712550381 1011882876085142142206393)
        ·
          refine ⟨758912157063856606654795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1011882876085142142206393 758912157063856606654795)
          ·
            refine ⟨1138368235595784909982193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758912157063856606654795 1138368235595784909982193)
            ·
              refine ⟨853776176696838682486645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1138368235595784909982193 853776176696838682486645)
              ·
                refine ⟨80041516565328626483123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 853776176696838682486645 80041516565328626483123)
                ·
                  rfl

theorem cell19_263048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_263048 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263048 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263048 prefixEnd_263048 := by exact prefixLift 263048
  have htrace : WordTrace (prefixWord ++ tailWord_263048) baseStart_263048 baseEnd_263048 := by
    simpa [prefixWord, tailWord_263048, baseEnd_263048] using wordTrace_append hprefix tailTrace_263048
  have hstable : (prefixWord ++ tailWord_263048).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263048).length < 2 ^ (prefixWord ++ tailWord_263048).sum := by decide
  have hdescent : baseEnd_263048 < baseStart_263048 := by decide
  rcases family_descends (prefixWord ++ tailWord_263048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263124 : List Nat := [2, 4, 1, 2, 1, 3, 6]
def baseStart_263124 : Nat := 118140960795 + 263124 * 2 ^ 59
def prefixEnd_263124 : Nat := 4983230072969 + 3 ^ 40 * 263124 * 2
def baseEnd_263124 : Nat := 26688214070860989598009

theorem tailTrace_263124 : CollatzResearch.WordTrace tailWord_263124 prefixEnd_263124 26688214070860989598009 := by
  unfold tailWord_263124
  simp only [CollatzResearch.WordTrace]
  refine ⟨4798460349377080423306213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6397947132502773897741617 4798460349377080423306213)
  ·
    refine ⟨899711315508202579369915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4798460349377080423306213 899711315508202579369915)
    ·
      refine ⟨1349566973262303869054873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 899711315508202579369915 1349566973262303869054873)
      ·
        refine ⟨1012175229946727901791155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1349566973262303869054873 1012175229946727901791155)
        ·
          refine ⟨1518262844920091852686733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1012175229946727901791155 1518262844920091852686733)
          ·
            refine ⟨569348566845034444757525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1518262844920091852686733 569348566845034444757525)
            ·
              refine ⟨26688214070860989598009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 569348566845034444757525 26688214070860989598009)
              ·
                rfl

theorem cell19_263124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 6].length) (baseStart_263124 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263124 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263124 prefixEnd_263124 := by exact prefixLift 263124
  have htrace : WordTrace (prefixWord ++ tailWord_263124) baseStart_263124 baseEnd_263124 := by
    simpa [prefixWord, tailWord_263124, baseEnd_263124] using wordTrace_append hprefix tailTrace_263124
  have hstable : (prefixWord ++ tailWord_263124).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263124).length < 2 ^ (prefixWord ++ tailWord_263124).sum := by decide
  have hdescent : baseEnd_263124 < baseStart_263124 := by decide
  rcases family_descends (prefixWord ++ tailWord_263124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263158 : List Nat := [5, 1, 1, 1, 3, 3, 2, 3]
def baseStart_263158 : Nat := 118140960795 + 263158 * 2 ^ 59
def prefixEnd_263158 : Nat := 4983230072969 + 3 ^ 40 * 263158 * 2
def baseEnd_263158 : Nat := 80074987896880964038379

theorem tailTrace_263158 : CollatzResearch.WordTrace tailWord_263158 prefixEnd_263158 80074987896880964038379 := by
  unfold tailWord_263158
  simp only [CollatzResearch.WordTrace]
  refine ⟨599885048789436540834383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6398773853753989768900085 599885048789436540834383)
  ·
    refine ⟨899827573184154811251575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 599885048789436540834383 899827573184154811251575)
    ·
      refine ⟨1349741359776232216877363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 899827573184154811251575 1349741359776232216877363)
      ·
        refine ⟨2024612039664348325316045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1349741359776232216877363 2024612039664348325316045)
        ·
          refine ⟨759229514874130621993517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2024612039664348325316045 759229514874130621993517)
          ·
            refine ⟨284711068077798983247569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 759229514874130621993517 284711068077798983247569)
            ·
              refine ⟨213533301058349237435677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284711068077798983247569 213533301058349237435677)
              ·
                refine ⟨80074987896880964038379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213533301058349237435677 80074987896880964038379)
                ·
                  rfl

theorem cell19_263158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_263158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263158 prefixEnd_263158 := by exact prefixLift 263158
  have htrace : WordTrace (prefixWord ++ tailWord_263158) baseStart_263158 baseEnd_263158 := by
    simpa [prefixWord, tailWord_263158, baseEnd_263158] using wordTrace_append hprefix tailTrace_263158
  have hstable : (prefixWord ++ tailWord_263158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263158).length < 2 ^ (prefixWord ++ tailWord_263158).sum := by decide
  have hdescent : baseEnd_263158 < baseStart_263158 := by decide
  rcases family_descends (prefixWord ++ tailWord_263158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263272 : List Nat := [2, 1, 4, 4, 1, 1, 3, 3]
def baseStart_263272 : Nat := 118140960795 + 263272 * 2 ^ 59
def prefixEnd_263272 : Nat := 4983230072969 + 3 ^ 40 * 263272 * 2
def baseEnd_263272 : Nat := 80109676367762477504735

theorem tailTrace_263272 : CollatzResearch.WordTrace tailWord_263272 prefixEnd_263272 80109676367762477504735 := by
  unfold tailWord_263272
  simp only [CollatzResearch.WordTrace]
  refine ⟨4801159351108991061500035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6401545801478654748666713 4801159351108991061500035)
  ·
    refine ⟨7201739026663486592250053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4801159351108991061500035 7201739026663486592250053)
    ·
      refine ⟨1350326067499403736046885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7201739026663486592250053 1350326067499403736046885)
      ·
        refine ⟨253186137656138200508791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1350326067499403736046885 253186137656138200508791)
        ·
          refine ⟨379779206484207300763187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253186137656138200508791 379779206484207300763187)
          ·
            refine ⟨569668809726310951144781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379779206484207300763187 569668809726310951144781)
            ·
              refine ⟨213625803647366606679293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 569668809726310951144781 213625803647366606679293)
              ·
                refine ⟨80109676367762477504735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213625803647366606679293 80109676367762477504735)
                ·
                  rfl

theorem cell19_263272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_263272 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263272 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263272 prefixEnd_263272 := by exact prefixLift 263272
  have htrace : WordTrace (prefixWord ++ tailWord_263272) baseStart_263272 baseEnd_263272 := by
    simpa [prefixWord, tailWord_263272, baseEnd_263272] using wordTrace_append hprefix tailTrace_263272
  have hstable : (prefixWord ++ tailWord_263272).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263272).length < 2 ^ (prefixWord ++ tailWord_263272).sum := by decide
  have hdescent : baseEnd_263272 < baseStart_263272 := by decide
  rcases family_descends (prefixWord ++ tailWord_263272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263274 : List Nat := [3, 1, 3, 2, 2, 2, 3, 3]
def baseStart_263274 : Nat := 118140960795 + 263274 * 2 ^ 59
def prefixEnd_263274 : Nat := 4983230072969 + 3 ^ 40 * 263274 * 2
def baseEnd_263274 : Nat := 80110284937427065460285

theorem tailTrace_263274 : CollatzResearch.WordTrace tailWord_263274 prefixEnd_263274 80110284937427065460285 := by
  unfold tailWord_263274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2400597912052684116143219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6401594432140490976381917 2400597912052684116143219)
  ·
    refine ⟨3600896868079026174214829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2400597912052684116143219 3600896868079026174214829)
    ·
      refine ⟨1350336325529634815330561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3600896868079026174214829 1350336325529634815330561)
      ·
        refine ⟨1012752244147226111497921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1350336325529634815330561 1012752244147226111497921)
        ·
          refine ⟨759564183110419583623441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1012752244147226111497921 759564183110419583623441)
          ·
            refine ⟨569673137332814687717581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 759564183110419583623441 569673137332814687717581)
            ·
              refine ⟨213627426499805507894093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 569673137332814687717581 213627426499805507894093)
              ·
                refine ⟨80110284937427065460285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213627426499805507894093 80110284937427065460285)
                ·
                  rfl

theorem cell19_263274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_263274 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263274 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263274 prefixEnd_263274 := by exact prefixLift 263274
  have htrace : WordTrace (prefixWord ++ tailWord_263274) baseStart_263274 baseEnd_263274 := by
    simpa [prefixWord, tailWord_263274, baseEnd_263274] using wordTrace_append hprefix tailTrace_263274
  have hstable : (prefixWord ++ tailWord_263274).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263274).length < 2 ^ (prefixWord ++ tailWord_263274).sum := by decide
  have hdescent : baseEnd_263274 < baseStart_263274 := by decide
  rcases family_descends (prefixWord ++ tailWord_263274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263276 : List Nat := [2, 2, 1, 1, 3, 2, 5, 3]
def baseStart_263276 : Nat := 118140960795 + 263276 * 2 ^ 59
def prefixEnd_263276 : Nat := 4983230072969 + 3 ^ 40 * 263276 * 2
def baseEnd_263276 : Nat := 80110893507091653415835

theorem tailTrace_263276 : CollatzResearch.WordTrace tailWord_263276 prefixEnd_263276 80110893507091653415835 := by
  unfold tailWord_263276
  simp only [CollatzResearch.WordTrace]
  refine ⟨4801232297101745403072841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6401643062802327204097121 4801232297101745403072841)
  ·
    refine ⟨3600924222826309052304631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4801232297101745403072841 3600924222826309052304631)
    ·
      refine ⟨5401386334239463578456947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3600924222826309052304631 5401386334239463578456947)
      ·
        refine ⟨8102079501359195367685421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5401386334239463578456947 8102079501359195367685421)
        ·
          refine ⟨3038279813009698262882033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8102079501359195367685421 3038279813009698262882033)
          ·
            refine ⟨2278709859757273697161525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3038279813009698262882033 2278709859757273697161525)
            ·
              refine ⟨213629049352244409108893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2278709859757273697161525 213629049352244409108893)
              ·
                refine ⟨80110893507091653415835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213629049352244409108893 80110893507091653415835)
                ·
                  rfl

theorem cell19_263276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_263276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263276 prefixEnd_263276 := by exact prefixLift 263276
  have htrace : WordTrace (prefixWord ++ tailWord_263276) baseStart_263276 baseEnd_263276 := by
    simpa [prefixWord, tailWord_263276, baseEnd_263276] using wordTrace_append hprefix tailTrace_263276
  have hstable : (prefixWord ++ tailWord_263276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263276).length < 2 ^ (prefixWord ++ tailWord_263276).sum := by decide
  have hdescent : baseEnd_263276 < baseStart_263276 := by decide
  rcases family_descends (prefixWord ++ tailWord_263276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263333 : List Nat := [1, 3, 1, 2, 1, 4, 4, 3]
def baseStart_263333 : Nat := 118140960795 + 263333 * 2 ^ 59
def prefixEnd_263333 : Nat := 4983230072969 + 3 ^ 40 * 263333 * 2
def baseEnd_263333 : Nat := 80128237742532410149013

theorem tailTrace_263333 : CollatzResearch.WordTrace tailWord_263333 prefixEnd_263333 80128237742532410149013 := by
  unfold tailWord_263333
  simp only [CollatzResearch.WordTrace]
  refine ⟨9604543554996989540970653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6403029036664659693980435 9604543554996989540970653)
  ·
    refine ⟨3601703833123871077863995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9604543554996989540970653 3601703833123871077863995)
    ·
      refine ⟨5402555749685806616795993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3601703833123871077863995 5402555749685806616795993)
      ·
        refine ⟨4051916812264354962596995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5402555749685806616795993 4051916812264354962596995)
        ·
          refine ⟨6077875218396532443895493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4051916812264354962596995 6077875218396532443895493)
          ·
            refine ⟨1139601603449349833230405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6077875218396532443895493 1139601603449349833230405)
            ·
              refine ⟨213675300646753093730701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1139601603449349833230405 213675300646753093730701)
              ·
                refine ⟨80128237742532410149013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213675300646753093730701 80128237742532410149013)
                ·
                  rfl

theorem cell19_263333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 3].length) (baseStart_263333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263333 prefixEnd_263333 := by exact prefixLift 263333
  have htrace : WordTrace (prefixWord ++ tailWord_263333) baseStart_263333 baseEnd_263333 := by
    simpa [prefixWord, tailWord_263333, baseEnd_263333] using wordTrace_append hprefix tailTrace_263333
  have hstable : (prefixWord ++ tailWord_263333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263333).length < 2 ^ (prefixWord ++ tailWord_263333).sum := by decide
  have hdescent : baseEnd_263333 < baseStart_263333 := by decide
  rcases family_descends (prefixWord ++ tailWord_263333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263392 : List Nat := [2, 1, 1, 3, 1, 4, 2, 5]
def baseStart_263392 : Nat := 118140960795 + 263392 * 2 ^ 59
def prefixEnd_263392 : Nat := 4983230072969 + 3 ^ 40 * 263392 * 2
def baseEnd_263392 : Nat := 80146190547637754837741

theorem tailTrace_263392 : CollatzResearch.WordTrace tailWord_263392 prefixEnd_263392 80146190547637754837741 := by
  unfold tailWord_263392
  simp only [CollatzResearch.WordTrace]
  refine ⟨4803347730891621308684215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6404463641188828411578953 4803347730891621308684215)
  ·
    refine ⟨7205021596337431963026323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4803347730891621308684215 7205021596337431963026323)
    ·
      refine ⟨10807532394506147944539485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7205021596337431963026323 10807532394506147944539485)
      ·
        refine ⟨4052824647939805479202307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10807532394506147944539485 4052824647939805479202307)
        ·
          refine ⟨6079236971909708218803461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4052824647939805479202307 6079236971909708218803461)
          ·
            refine ⟨1139856932233070291025649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6079236971909708218803461 1139856932233070291025649)
            ·
              refine ⟨854892699174802718269237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1139856932233070291025649 854892699174802718269237)
              ·
                refine ⟨80146190547637754837741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 854892699174802718269237 80146190547637754837741)
                ·
                  rfl

theorem cell19_263392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_263392 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263392 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263392 prefixEnd_263392 := by exact prefixLift 263392
  have htrace : WordTrace (prefixWord ++ tailWord_263392) baseStart_263392 baseEnd_263392 := by
    simpa [prefixWord, tailWord_263392, baseEnd_263392] using wordTrace_append hprefix tailTrace_263392
  have hstable : (prefixWord ++ tailWord_263392).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263392).length < 2 ^ (prefixWord ++ tailWord_263392).sum := by decide
  have hdescent : baseEnd_263392 < baseStart_263392 := by decide
  rcases family_descends (prefixWord ++ tailWord_263392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263428 : List Nat := [2, 3, 2, 2, 2, 1, 3, 4]
def baseStart_263428 : Nat := 118140960795 + 263428 * 2 ^ 59
def prefixEnd_263428 : Nat := 4983230072969 + 3 ^ 40 * 263428 * 2
def baseEnd_263428 : Nat := 80157144801600338037643

theorem tailTrace_263428 : CollatzResearch.WordTrace tailWord_263428 prefixEnd_263428 80157144801600338037643 := by
  unfold tailWord_263428
  simp only [CollatzResearch.WordTrace]
  refine ⟨4804004244826410382839469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6405338993101880510452625 4804004244826410382839469)
  ·
    refine ⟨1801501591809903893564801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4804004244826410382839469 1801501591809903893564801)
    ·
      refine ⟨1351126193857427920173601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1801501591809903893564801 1351126193857427920173601)
      ·
        refine ⟨1013344645393070940130201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1351126193857427920173601 1013344645393070940130201)
        ·
          refine ⟨760008484044803205097651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1013344645393070940130201 760008484044803205097651)
          ·
            refine ⟨1140012726067204807646477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760008484044803205097651 1140012726067204807646477)
            ·
              refine ⟨427504772275201802867429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1140012726067204807646477 427504772275201802867429)
              ·
                refine ⟨80157144801600338037643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 427504772275201802867429 80157144801600338037643)
                ·
                  rfl

theorem cell19_263428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_263428 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263428 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263428 prefixEnd_263428 := by exact prefixLift 263428
  have htrace : WordTrace (prefixWord ++ tailWord_263428) baseStart_263428 baseEnd_263428 := by
    simpa [prefixWord, tailWord_263428, baseEnd_263428] using wordTrace_append hprefix tailTrace_263428
  have hstable : (prefixWord ++ tailWord_263428).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263428).length < 2 ^ (prefixWord ++ tailWord_263428).sum := by decide
  have hdescent : baseEnd_263428 < baseStart_263428 := by decide
  rcases family_descends (prefixWord ++ tailWord_263428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263447 : List Nat := [1, 1, 3, 4, 1, 1, 5, 3]
def baseStart_263447 : Nat := 118140960795 + 263447 * 2 ^ 59
def prefixEnd_263447 : Nat := 4983230072969 + 3 ^ 40 * 263447 * 2
def baseEnd_263447 : Nat := 80162926213413923615369

theorem tailTrace_263447 : CollatzResearch.WordTrace tailWord_263447 prefixEnd_263447 80162926213413923615369 := by
  unfold tailWord_263447
  simp only [CollatzResearch.WordTrace]
  refine ⟨9608701476583987010620595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6405800984389324673747063 9608701476583987010620595)
  ·
    refine ⟨14413052214875980515930893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9608701476583987010620595 14413052214875980515930893)
    ·
      refine ⟨5404894580578492693474085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14413052214875980515930893 5404894580578492693474085)
      ·
        refine ⟨1013417733858467380026391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5404894580578492693474085 1013417733858467380026391)
        ·
          refine ⟨1520126600787701070039587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1013417733858467380026391 1520126600787701070039587)
          ·
            refine ⟨2280189901181551605059381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1520126600787701070039587 2280189901181551605059381)
            ·
              refine ⟨213767803235770462974317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2280189901181551605059381 213767803235770462974317)
              ·
                refine ⟨80162926213413923615369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213767803235770462974317 80162926213413923615369)
                ·
                  rfl

theorem cell19_263447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 3].length) (baseStart_263447 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263447 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263447 prefixEnd_263447 := by exact prefixLift 263447
  have htrace : WordTrace (prefixWord ++ tailWord_263447) baseStart_263447 baseEnd_263447 := by
    simpa [prefixWord, tailWord_263447, baseEnd_263447] using wordTrace_append hprefix tailTrace_263447
  have hstable : (prefixWord ++ tailWord_263447).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263447).length < 2 ^ (prefixWord ++ tailWord_263447).sum := by decide
  have hdescent : baseEnd_263447 < baseStart_263447 := by decide
  rcases family_descends (prefixWord ++ tailWord_263447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263466 : List Nat := [3, 1, 4, 2, 1, 2, 6]
def baseStart_263466 : Nat := 118140960795 + 263466 * 2 ^ 59
def prefixEnd_263466 : Nat := 4983230072969 + 3 ^ 40 * 263466 * 2
def baseEnd_263466 : Nat := 26722902541742503064365

theorem tailTrace_263466 : CollatzResearch.WordTrace tailWord_263466 prefixEnd_263466 26722902541742503064365 := by
  unfold tailWord_263466
  simp only [CollatzResearch.WordTrace]
  refine ⟨2402348615878788313890563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6406262975676768837041501 2402348615878788313890563)
  ·
    refine ⟨3603522923818182470835845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2402348615878788313890563 3603522923818182470835845)
    ·
      refine ⟨675660548215909213281721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3603522923818182470835845 675660548215909213281721)
      ·
        refine ⟨506745411161931909961291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675660548215909213281721 506745411161931909961291)
        ·
          refine ⟨760118116742897864941937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506745411161931909961291 760118116742897864941937)
          ·
            refine ⟨570088587557173398706453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 760118116742897864941937 570088587557173398706453)
            ·
              refine ⟨26722902541742503064365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 570088587557173398706453 26722902541742503064365)
              ·
                rfl

theorem cell19_263466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 6].length) (baseStart_263466 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263466 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263466 prefixEnd_263466 := by exact prefixLift 263466
  have htrace : WordTrace (prefixWord ++ tailWord_263466) baseStart_263466 baseEnd_263466 := by
    simpa [prefixWord, tailWord_263466, baseEnd_263466] using wordTrace_append hprefix tailTrace_263466
  have hstable : (prefixWord ++ tailWord_263466).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263466).length < 2 ^ (prefixWord ++ tailWord_263466).sum := by decide
  have hdescent : baseEnd_263466 < baseStart_263466 := by decide
  rcases family_descends (prefixWord ++ tailWord_263466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263517 : List Nat := [1, 4, 5, 1, 2, 1, 5]
def baseStart_263517 : Nat := 118140960795 + 263517 * 2 ^ 59
def prefixEnd_263517 : Nat := 4983230072969 + 3 ^ 40 * 263517 * 2
def baseEnd_263517 : Nat := 26728075383891500686541

theorem tailTrace_263517 : CollatzResearch.WordTrace tailWord_263517 prefixEnd_263517 26728075383891500686541 := by
  unfold tailWord_263517
  simp only [CollatzResearch.WordTrace]
  refine ⟨9611254586330388965668805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6407503057553592643779203 9611254586330388965668805)
  ·
    refine ⟨1802110234936947931062901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9611254586330388965668805 1802110234936947931062901)
    ·
      refine ⟨168947834525338868537147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1802110234936947931062901 168947834525338868537147)
      ·
        refine ⟨253421751788008302805721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168947834525338868537147 253421751788008302805721)
        ·
          refine ⟨190066313841006227104291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253421751788008302805721 190066313841006227104291)
          ·
            refine ⟨285099470761509340656437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190066313841006227104291 285099470761509340656437)
            ·
              refine ⟨26728075383891500686541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 285099470761509340656437 26728075383891500686541)
              ·
                rfl

theorem cell19_263517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 5].length) (baseStart_263517 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263517 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263517 prefixEnd_263517 := by exact prefixLift 263517
  have htrace : WordTrace (prefixWord ++ tailWord_263517) baseStart_263517 baseEnd_263517 := by
    simpa [prefixWord, tailWord_263517, baseEnd_263517] using wordTrace_append hprefix tailTrace_263517
  have hstable : (prefixWord ++ tailWord_263517).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263517).length < 2 ^ (prefixWord ++ tailWord_263517).sum := by decide
  have hdescent : baseEnd_263517 < baseStart_263517 := by decide
  rcases family_descends (prefixWord ++ tailWord_263517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263580 : List Nat := [2, 2, 3, 4, 1, 7]
def baseStart_263580 : Nat := 118140960795 + 263580 * 2 ^ 59
def prefixEnd_263580 : Nat := 4983230072969 + 3 ^ 40 * 263580 * 2
def baseEnd_263580 : Nat := 8911488455123224739939

theorem tailTrace_263580 : CollatzResearch.WordTrace tailWord_263580 prefixEnd_263580 8911488455123224739939 := by
  unfold tailWord_263580
  simp only [CollatzResearch.WordTrace]
  refine ⟨4806776192551075362606097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6409034923401433816808129 4806776192551075362606097)
  ·
    refine ⟨3605082144413306521954573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4806776192551075362606097 3605082144413306521954573)
    ·
      refine ⟨1351905804154989945732965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3605082144413306521954573 1351905804154989945732965)
      ·
        refine ⟨253482338279060614824931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1351905804154989945732965 253482338279060614824931)
        ·
          refine ⟨380223507418590922237397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253482338279060614824931 380223507418590922237397)
          ·
            refine ⟨8911488455123224739939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 380223507418590922237397 8911488455123224739939)
            ·
              rfl

theorem cell19_263580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 7].length) (baseStart_263580 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263580 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263580 prefixEnd_263580 := by exact prefixLift 263580
  have htrace : WordTrace (prefixWord ++ tailWord_263580) baseStart_263580 baseEnd_263580 := by
    simpa [prefixWord, tailWord_263580, baseEnd_263580] using wordTrace_append hprefix tailTrace_263580
  have hstable : (prefixWord ++ tailWord_263580).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263580).length < 2 ^ (prefixWord ++ tailWord_263580).sum := by decide
  have hdescent : baseEnd_263580 < baseStart_263580 := by decide
  rcases family_descends (prefixWord ++ tailWord_263580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263597 : List Nat := [1, 5, 2, 2, 1, 3, 1, 4]
def baseStart_263597 : Nat := 118140960795 + 263597 * 2 ^ 59
def prefixEnd_263597 : Nat := 4983230072969 + 3 ^ 40 * 263597 * 2
def baseEnd_263597 : Nat := 80208568938258020281627

theorem tailTrace_263597 : CollatzResearch.WordTrace tailWord_263597 prefixEnd_263597 80208568938258020281627 := by
  unfold tailWord_263597
  simp only [CollatzResearch.WordTrace]
  refine ⟨9614172426040562628581045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6409448284027041752387363 9614172426040562628581045)
  ·
    refine ⟨901328664941302746429473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9614172426040562628581045 901328664941302746429473)
    ·
      refine ⟨675996498705977059822105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 901328664941302746429473 675996498705977059822105)
      ·
        refine ⟨506997374029482794866579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675996498705977059822105 506997374029482794866579)
        ·
          refine ⟨760496061044224192299869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506997374029482794866579 760496061044224192299869)
          ·
            refine ⟨285186022891584072112451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 760496061044224192299869 285186022891584072112451)
            ·
              refine ⟨427779034337376108168677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285186022891584072112451 427779034337376108168677)
              ·
                refine ⟨80208568938258020281627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 427779034337376108168677 80208568938258020281627)
                ·
                  rfl

theorem cell19_263597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 4].length) (baseStart_263597 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263597 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263597 prefixEnd_263597 := by exact prefixLift 263597
  have htrace : WordTrace (prefixWord ++ tailWord_263597) baseStart_263597 baseEnd_263597 := by
    simpa [prefixWord, tailWord_263597, baseEnd_263597] using wordTrace_append hprefix tailTrace_263597
  have hstable : (prefixWord ++ tailWord_263597).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263597).length < 2 ^ (prefixWord ++ tailWord_263597).sum := by decide
  have hdescent : baseEnd_263597 < baseStart_263597 := by decide
  rcases family_descends (prefixWord ++ tailWord_263597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263677 : List Nat := [1, 4, 1, 1, 1, 5, 1, 5]
def baseStart_263677 : Nat := 118140960795 + 263677 * 2 ^ 59
def prefixEnd_263677 : Nat := 4983230072969 + 3 ^ 40 * 263677 * 2
def baseEnd_263677 : Nat := 80232911724841538503631

theorem tailTrace_263677 : CollatzResearch.WordTrace tailWord_263677 prefixEnd_263677 80232911724841538503631 := by
  unfold tailWord_263677
  simp only [CollatzResearch.WordTrace]
  refine ⟨9617090265750736291493285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6411393510500490860995523 9617090265750736291493285)
  ·
    refine ⟨1803204424828263054654991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9617090265750736291493285 1803204424828263054654991)
    ·
      refine ⟨2704806637242394581982487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1803204424828263054654991 2704806637242394581982487)
      ·
        refine ⟨4057209955863591872973731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2704806637242394581982487 4057209955863591872973731)
        ·
          refine ⟨6085814933795387809460597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4057209955863591872973731 6085814933795387809460597)
          ·
            refine ⟨570545150043317607136931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6085814933795387809460597 570545150043317607136931)
            ·
              refine ⟨855817725064976410705397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570545150043317607136931 855817725064976410705397)
              ·
                refine ⟨80232911724841538503631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 855817725064976410705397 80232911724841538503631)
                ·
                  rfl

theorem cell19_263677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_263677 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263677 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263677 prefixEnd_263677 := by exact prefixLift 263677
  have htrace : WordTrace (prefixWord ++ tailWord_263677) baseStart_263677 baseEnd_263677 := by
    simpa [prefixWord, tailWord_263677, baseEnd_263677] using wordTrace_append hprefix tailTrace_263677
  have hstable : (prefixWord ++ tailWord_263677).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263677).length < 2 ^ (prefixWord ++ tailWord_263677).sum := by decide
  have hdescent : baseEnd_263677 < baseStart_263677 := by decide
  rcases family_descends (prefixWord ++ tailWord_263677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263694 : List Nat := [4, 1, 1, 2, 4, 2, 5]
def baseStart_263694 : Nat := 118140960795 + 263694 * 2 ^ 59
def prefixEnd_263694 : Nat := 4983230072969 + 3 ^ 40 * 263694 * 2
def baseEnd_263694 : Nat := 26746028188996845375269

theorem tailTrace_263694 : CollatzResearch.WordTrace tailWord_263694 prefixEnd_263694 26746028188996845375269 := by
  unfold tailWord_263694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1202213788336143524357767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6411806871126098796574757 1202213788336143524357767)
  ·
    refine ⟨1803320682504215286536651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1202213788336143524357767 1803320682504215286536651)
    ·
      refine ⟨2704981023756322929804977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1803320682504215286536651 2704981023756322929804977)
      ·
        refine ⟨2028735767817242197353733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2704981023756322929804977 2028735767817242197353733)
        ·
          refine ⟨380387956465732912003825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2028735767817242197353733 380387956465732912003825)
          ·
            refine ⟨285290967349299684002869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380387956465732912003825 285290967349299684002869)
            ·
              refine ⟨26746028188996845375269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 285290967349299684002869 26746028188996845375269)
              ·
                rfl

theorem cell19_263694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 5].length) (baseStart_263694 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263694 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263694 prefixEnd_263694 := by exact prefixLift 263694
  have htrace : WordTrace (prefixWord ++ tailWord_263694) baseStart_263694 baseEnd_263694 := by
    simpa [prefixWord, tailWord_263694, baseEnd_263694] using wordTrace_append hprefix tailTrace_263694
  have hstable : (prefixWord ++ tailWord_263694).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263694).length < 2 ^ (prefixWord ++ tailWord_263694).sum := by decide
  have hdescent : baseEnd_263694 < baseStart_263694 := by decide
  rcases family_descends (prefixWord ++ tailWord_263694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263793 : List Nat := [1, 2, 2, 2, 1, 1, 1, 9]
def baseStart_263793 : Nat := 118140960795 + 263793 * 2 ^ 59
def prefixEnd_263793 : Nat := 4983230072969 + 3 ^ 40 * 263793 * 2
def baseEnd_263793 : Nat := 80268208765387639925537

theorem tailTrace_263793 : CollatzResearch.WordTrace tailWord_263793 prefixEnd_263793 80268208765387639925537 := by
  unfold tailWord_263793
  simp only [CollatzResearch.WordTrace]
  refine ⟨9621321133330488102716033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6414214088886992068477355 9621321133330488102716033)
  ·
    refine ⟨7215990849997866077037025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9621321133330488102716033 7215990849997866077037025)
    ·
      refine ⟨5411993137498399557777769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7215990849997866077037025 5411993137498399557777769)
      ·
        refine ⟨4058994853123799668333327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5411993137498399557777769 4058994853123799668333327)
        ·
          refine ⟨6088492279685699502499991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4058994853123799668333327 6088492279685699502499991)
          ·
            refine ⟨9132738419528549253749987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6088492279685699502499991 9132738419528549253749987)
            ·
              refine ⟨13699107629292823880624981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9132738419528549253749987 13699107629292823880624981)
              ·
                refine ⟨80268208765387639925537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13699107629292823880624981 80268208765387639925537)
                ·
                  rfl

theorem cell19_263793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_263793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263793 prefixEnd_263793 := by exact prefixLift 263793
  have htrace : WordTrace (prefixWord ++ tailWord_263793) baseStart_263793 baseEnd_263793 := by
    simpa [prefixWord, tailWord_263793, baseEnd_263793] using wordTrace_append hprefix tailTrace_263793
  have hstable : (prefixWord ++ tailWord_263793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263793).length < 2 ^ (prefixWord ++ tailWord_263793).sum := by decide
  have hdescent : baseEnd_263793 < baseStart_263793 := by decide
  rcases family_descends (prefixWord ++ tailWord_263793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263842 : List Nat := [3, 3, 1, 4, 1, 2, 2, 3]
def baseStart_263842 : Nat := 118140960795 + 263842 * 2 ^ 59
def prefixEnd_263842 : Nat := 4983230072969 + 3 ^ 40 * 263842 * 2
def baseEnd_263842 : Nat := 80283118722170044836515

theorem tailTrace_263842 : CollatzResearch.WordTrace tailWord_263842 prefixEnd_263842 80283118722170044836515 := by
  unfold tailWord_263842
  simp only [CollatzResearch.WordTrace]
  refine ⟨2405777077538242367812445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6415405540101979647499853 2405777077538242367812445)
  ·
    refine ⟨902166404076840887929667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2405777077538242367812445 902166404076840887929667)
    ·
      refine ⟨1353249606115261331894501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 902166404076840887929667 1353249606115261331894501)
      ·
        refine ⟨253734301146611499730219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1353249606115261331894501 253734301146611499730219)
        ·
          refine ⟨380601451719917249595329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253734301146611499730219 380601451719917249595329)
          ·
            refine ⟨285451088789937937196497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380601451719917249595329 285451088789937937196497)
            ·
              refine ⟨214088316592453452897373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285451088789937937196497 214088316592453452897373)
              ·
                refine ⟨80283118722170044836515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214088316592453452897373 80283118722170044836515)
                ·
                  rfl

theorem cell19_263842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_263842 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263842 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263842 prefixEnd_263842 := by exact prefixLift 263842
  have htrace : WordTrace (prefixWord ++ tailWord_263842) baseStart_263842 baseEnd_263842 := by
    simpa [prefixWord, tailWord_263842, baseEnd_263842] using wordTrace_append hprefix tailTrace_263842
  have hstable : (prefixWord ++ tailWord_263842).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263842).length < 2 ^ (prefixWord ++ tailWord_263842).sum := by decide
  have hdescent : baseEnd_263842 < baseStart_263842 := by decide
  rcases family_descends (prefixWord ++ tailWord_263842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263884 : List Nat := [2, 2, 1, 5, 2, 1, 2, 4]
def baseStart_263884 : Nat := 118140960795 + 263884 * 2 ^ 59
def prefixEnd_263884 : Nat := 4983230072969 + 3 ^ 40 * 263884 * 2
def baseEnd_263884 : Nat := 80295898685126391903067

theorem tailTrace_263884 : CollatzResearch.WordTrace tailWord_263884 prefixEnd_263884 80295898685126391903067 := by
  unfold tailWord_263884
  simp only [CollatzResearch.WordTrace]
  refine ⟨4812320088000405322139353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6416426784000540429519137 4812320088000405322139353)
  ·
    refine ⟨3609240066000303991604515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4812320088000405322139353 3609240066000303991604515)
    ·
      refine ⟨5413860099000455987406773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3609240066000303991604515 5413860099000455987406773)
      ·
        refine ⟨507549384281292748819385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5413860099000455987406773 507549384281292748819385)
        ·
          refine ⟨380662038210969561614539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507549384281292748819385 380662038210969561614539)
          ·
            refine ⟨570993057316454342421809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380662038210969561614539 570993057316454342421809)
            ·
              refine ⟨428244792987340756816357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570993057316454342421809 428244792987340756816357)
              ·
                refine ⟨80295898685126391903067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 428244792987340756816357 80295898685126391903067)
                ·
                  rfl

theorem cell19_263884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_263884 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263884 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263884 prefixEnd_263884 := by exact prefixLift 263884
  have htrace : WordTrace (prefixWord ++ tailWord_263884) baseStart_263884 baseEnd_263884 := by
    simpa [prefixWord, tailWord_263884, baseEnd_263884] using wordTrace_append hprefix tailTrace_263884
  have hstable : (prefixWord ++ tailWord_263884).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263884).length < 2 ^ (prefixWord ++ tailWord_263884).sum := by decide
  have hdescent : baseEnd_263884 < baseStart_263884 := by decide
  rcases family_descends (prefixWord ++ tailWord_263884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263886 : List Nat := [4, 1, 1, 1, 3, 1, 4, 4]
def baseStart_263886 : Nat := 118140960795 + 263886 * 2 ^ 59
def prefixEnd_263886 : Nat := 4983230072969 + 3 ^ 40 * 263886 * 2
def baseEnd_263886 : Nat := 80296507254790979858617

theorem tailTrace_263886 : CollatzResearch.WordTrace tailWord_263886 prefixEnd_263886 80296507254790979858617 := by
  unfold tailWord_263886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1203089140249195623231439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6416475414662376657234341 1203089140249195623231439)
  ·
    refine ⟨1804633710373793434847159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1203089140249195623231439 1804633710373793434847159)
    ·
      refine ⟨2706950565560690152270739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1804633710373793434847159 2706950565560690152270739)
      ·
        refine ⟨4060425848341035228406109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2706950565560690152270739 4060425848341035228406109)
        ·
          refine ⟨1522659693127888210652291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4060425848341035228406109 1522659693127888210652291)
          ·
            refine ⟨2283989539691832315978437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1522659693127888210652291 2283989539691832315978437)
            ·
              refine ⟨428248038692218559245957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2283989539691832315978437 428248038692218559245957)
              ·
                refine ⟨80296507254790979858617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 428248038692218559245957 80296507254790979858617)
                ·
                  rfl

theorem cell19_263886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_263886 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_263886 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_263886 prefixEnd_263886 := by exact prefixLift 263886
  have htrace : WordTrace (prefixWord ++ tailWord_263886) baseStart_263886 baseEnd_263886 := by
    simpa [prefixWord, tailWord_263886, baseEnd_263886] using wordTrace_append hprefix tailTrace_263886
  have hstable : (prefixWord ++ tailWord_263886).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263886).length < 2 ^ (prefixWord ++ tailWord_263886).sum := by decide
  have hdescent : baseEnd_263886 < baseStart_263886 := by decide
  rcases family_descends (prefixWord ++ tailWord_263886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264017 : List Nat := [1, 2, 2, 1, 5, 3, 2, 3]
def baseStart_264017 : Nat := 118140960795 + 264017 * 2 ^ 59
def prefixEnd_264017 : Nat := 4983230072969 + 3 ^ 40 * 264017 * 2
def baseEnd_264017 : Nat := 80336368567821490947149

theorem tailTrace_264017 : CollatzResearch.WordTrace tailWord_264017 prefixEnd_264017 80336368567821490947149 := by
  unfold tailWord_264017
  simp only [CollatzResearch.WordTrace]
  refine ⟨9629491084518974358870305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6419660723012649572580203 9629491084518974358870305)
  ·
    refine ⟨7222118313389230769152729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9629491084518974358870305 7222118313389230769152729)
    ·
      refine ⟨5416588735041923076864547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7222118313389230769152729 5416588735041923076864547)
      ·
        refine ⟨8124883102562884615296821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5416588735041923076864547 8124883102562884615296821)
        ·
          refine ⟨761707790865270432684077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8124883102562884615296821 761707790865270432684077)
          ·
            refine ⟨285640421574476412256529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 761707790865270432684077 285640421574476412256529)
            ·
              refine ⟨214230316180857309192397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285640421574476412256529 214230316180857309192397)
              ·
                refine ⟨80336368567821490947149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214230316180857309192397 80336368567821490947149)
                ·
                  rfl

theorem cell19_264017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 3].length) (baseStart_264017 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_264017 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_264017 prefixEnd_264017 := by exact prefixLift 264017
  have htrace : WordTrace (prefixWord ++ tailWord_264017) baseStart_264017 baseEnd_264017 := by
    simpa [prefixWord, tailWord_264017, baseEnd_264017] using wordTrace_append hprefix tailTrace_264017
  have hstable : (prefixWord ++ tailWord_264017).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264017).length < 2 ^ (prefixWord ++ tailWord_264017).sum := by decide
  have hdescent : baseEnd_264017 < baseStart_264017 := by decide
  rcases family_descends (prefixWord ++ tailWord_264017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264036 : List Nat := [2, 3, 1, 1, 6, 1, 5]
def baseStart_264036 : Nat := 118140960795 + 264036 * 2 ^ 59
def prefixEnd_264036 : Nat := 4983230072969 + 3 ^ 40 * 264036 * 2
def baseEnd_264036 : Nat := 26780716659878358841625

theorem tailTrace_264036 : CollatzResearch.WordTrace tailWord_264036 prefixEnd_264036 26780716659878358841625 := by
  unfold tailWord_264036
  simp only [CollatzResearch.WordTrace]
  refine ⟨4815092035725070301905981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6420122714300093735874641 4815092035725070301905981)
  ·
    refine ⟨1805659513396901363214743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4815092035725070301905981 1805659513396901363214743)
    ·
      refine ⟨2708489270095352044822115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1805659513396901363214743 2708489270095352044822115)
      ·
        refine ⟨4062733905143028067233173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2708489270095352044822115 4062733905143028067233173)
        ·
          refine ⟨190440651803579440651555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4062733905143028067233173 190440651803579440651555)
          ·
            refine ⟨285660977705369160977333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190440651803579440651555 285660977705369160977333)
            ·
              refine ⟨26780716659878358841625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 285660977705369160977333 26780716659878358841625)
              ·
                rfl

theorem cell19_264036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 5].length) (baseStart_264036 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_264036 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_264036 prefixEnd_264036 := by exact prefixLift 264036
  have htrace : WordTrace (prefixWord ++ tailWord_264036) baseStart_264036 baseEnd_264036 := by
    simpa [prefixWord, tailWord_264036, baseEnd_264036] using wordTrace_append hprefix tailTrace_264036
  have hstable : (prefixWord ++ tailWord_264036).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264036).length < 2 ^ (prefixWord ++ tailWord_264036).sum := by decide
  have hdescent : baseEnd_264036 < baseStart_264036 := by decide
  rcases family_descends (prefixWord ++ tailWord_264036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264095 : List Nat := [1, 1, 2, 5, 4, 6]
def baseStart_264095 : Nat := 118140960795 + 264095 * 2 ^ 59
def prefixEnd_264095 : Nat := 4983230072969 + 3 ^ 40 * 264095 * 2
def baseEnd_264095 : Nat := 8928900309415602357067

theorem tailTrace_264095 : CollatzResearch.WordTrace tailWord_264095 prefixEnd_264095 8928900309415602357067 := by
  unfold tailWord_264095
  simp only [CollatzResearch.WordTrace]
  refine ⟨9632335978236393680209739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6421557318824262453473159 9632335978236393680209739)
  ·
    refine ⟨14448503967354590520314609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9632335978236393680209739 14448503967354590520314609)
    ·
      refine ⟨10836377975515942890235957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14448503967354590520314609 10836377975515942890235957)
      ·
        refine ⟨1015910435204619645959621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10836377975515942890235957 1015910435204619645959621)
        ·
          refine ⟨190483206600866183617429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1015910435204619645959621 190483206600866183617429)
          ·
            refine ⟨8928900309415602357067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 190483206600866183617429 8928900309415602357067)
            ·
              rfl

theorem cell19_264095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 6].length) (baseStart_264095 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_264095 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_264095 prefixEnd_264095 := by exact prefixLift 264095
  have htrace : WordTrace (prefixWord ++ tailWord_264095) baseStart_264095 baseEnd_264095 := by
    simpa [prefixWord, tailWord_264095, baseEnd_264095] using wordTrace_append hprefix tailTrace_264095
  have hstable : (prefixWord ++ tailWord_264095).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264095).length < 2 ^ (prefixWord ++ tailWord_264095).sum := by decide
  have hdescent : baseEnd_264095 < baseStart_264095 := by decide
  rcases family_descends (prefixWord ++ tailWord_264095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264097 : List Nat := [1, 2, 3, 4, 9]
def baseStart_264097 : Nat := 118140960795 + 264097 * 2 ^ 59
def prefixEnd_264097 : Nat := 4983230072969 + 3 ^ 40 * 264097 * 2
def baseEnd_264097 : Nat := 2976322642755741080339

theorem tailTrace_264097 : CollatzResearch.WordTrace tailWord_264097 prefixEnd_264097 2976322642755741080339 := by
  unfold tailWord_264097
  simp only [CollatzResearch.WordTrace]
  refine ⟨9632408924229148021782545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6421605949486098681188363 9632408924229148021782545)
  ·
    refine ⟨7224306693171861016336909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9632408924229148021782545 7224306693171861016336909)
    ·
      refine ⟨2709115009939447881126341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7224306693171861016336909 2709115009939447881126341)
      ·
        refine ⟨507959064363646477711189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2709115009939447881126341 507959064363646477711189)
        ·
          refine ⟨2976322642755741080339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 507959064363646477711189 2976322642755741080339)
          ·
            rfl

theorem cell19_264097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 9].length) (baseStart_264097 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_264097 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_264097 prefixEnd_264097 := by exact prefixLift 264097
  have htrace : WordTrace (prefixWord ++ tailWord_264097) baseStart_264097 baseEnd_264097 := by
    simpa [prefixWord, tailWord_264097, baseEnd_264097] using wordTrace_append hprefix tailTrace_264097
  have hstable : (prefixWord ++ tailWord_264097).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264097).length < 2 ^ (prefixWord ++ tailWord_264097).sum := by decide
  have hdescent : baseEnd_264097 < baseStart_264097 := by decide
  rcases family_descends (prefixWord ++ tailWord_264097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264150 : List Nat := [5, 2, 1, 1, 3, 1, 6]
def baseStart_264150 : Nat := 118140960795 + 264150 * 2 ^ 59
def prefixEnd_264150 : Nat := 4983230072969 + 3 ^ 40 * 264150 * 2
def baseEnd_264150 : Nat := 26792279483505529997077

theorem tailTrace_264150 : CollatzResearch.WordTrace tailWord_264150 prefixEnd_264150 26792279483505529997077 := by
  unfold tailWord_264150
  simp only [CollatzResearch.WordTrace]
  refine ⟨602146374564821129591369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6422894662024758715641269 602146374564821129591369)
  ·
    refine ⟨451609780923615847193527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 602146374564821129591369 451609780923615847193527)
    ·
      refine ⟨677414671385423770790291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451609780923615847193527 677414671385423770790291)
      ·
        refine ⟨1016122007078135656185437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677414671385423770790291 1016122007078135656185437)
        ·
          refine ⟨381045752654300871069539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1016122007078135656185437 381045752654300871069539)
          ·
            refine ⟨571568628981451306604309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381045752654300871069539 571568628981451306604309)
            ·
              refine ⟨26792279483505529997077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 571568628981451306604309 26792279483505529997077)
              ·
                rfl

theorem cell19_264150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 6].length) (baseStart_264150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_264150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_264150 prefixEnd_264150 := by exact prefixLift 264150
  have htrace : WordTrace (prefixWord ++ tailWord_264150) baseStart_264150 baseEnd_264150 := by
    simpa [prefixWord, tailWord_264150, baseEnd_264150] using wordTrace_append hprefix tailTrace_264150
  have hstable : (prefixWord ++ tailWord_264150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264150).length < 2 ^ (prefixWord ++ tailWord_264150).sum := by decide
  have hdescent : baseEnd_264150 < baseStart_264150 := by decide
  rcases family_descends (prefixWord ++ tailWord_264150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264304 : List Nat := [2, 1, 1, 1, 5, 3, 3, 3]
def baseStart_264304 : Nat := 118140960795 + 264304 * 2 ^ 59
def prefixEnd_264304 : Nat := 4983230072969 + 3 ^ 40 * 264304 * 2
def baseEnd_264304 : Nat := 80423698314689862568589

theorem tailTrace_264304 : CollatzResearch.WordTrace tailWord_264304 prefixEnd_264304 80423698314689862568589 := by
  unfold tailWord_264304
  simp only [CollatzResearch.WordTrace]
  refine ⟨4819979417239611187283983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6426639222986148249711977 4819979417239611187283983)
  ·
    refine ⟨7229969125859416780925975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4819979417239611187283983 7229969125859416780925975)
    ·
      refine ⟨10844953688789125171388963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7229969125859416780925975 10844953688789125171388963)
      ·
        refine ⟨16267430533183687757083445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10844953688789125171388963 16267430533183687757083445)
        ·
          refine ⟨1525071612485970727226573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16267430533183687757083445 1525071612485970727226573)
          ·
            refine ⟨571901854682239022709965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1525071612485970727226573 571901854682239022709965)
            ·
              refine ⟨214463195505839633516237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 571901854682239022709965 214463195505839633516237)
              ·
                refine ⟨80423698314689862568589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214463195505839633516237 80423698314689862568589)
                ·
                  rfl

theorem cell19_264304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_264304 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_264304 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_264304 prefixEnd_264304 := by exact prefixLift 264304
  have htrace : WordTrace (prefixWord ++ tailWord_264304) baseStart_264304 baseEnd_264304 := by
    simpa [prefixWord, tailWord_264304, baseEnd_264304] using wordTrace_append hprefix tailTrace_264304
  have hstable : (prefixWord ++ tailWord_264304).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264304).length < 2 ^ (prefixWord ++ tailWord_264304).sum := by decide
  have hdescent : baseEnd_264304 < baseStart_264304 := by decide
  rcases family_descends (prefixWord ++ tailWord_264304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264325 : List Nat := [1, 3, 1, 1, 5, 2, 6]
def baseStart_264325 : Nat := 118140960795 + 264325 * 2 ^ 59
def prefixEnd_264325 : Nat := 4983230072969 + 3 ^ 40 * 264325 * 2
def baseEnd_264325 : Nat := 26810029432056012033955

theorem tailTrace_264325 : CollatzResearch.WordTrace tailWord_264325 prefixEnd_264325 26810029432056012033955 := by
  unfold tailWord_264325
  simp only [CollatzResearch.WordTrace]
  refine ⟨9640724767403142961082429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6427149844935428640721619 9640724767403142961082429)
  ·
    refine ⟨3615271787776178610405911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9640724767403142961082429 3615271787776178610405911)
    ·
      refine ⟨5422907681664267915608867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3615271787776178610405911 5422907681664267915608867)
      ·
        refine ⟨8134361522496401873413301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5422907681664267915608867 8134361522496401873413301)
        ·
          refine ⟨762596392734037675632497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8134361522496401873413301 762596392734037675632497)
          ·
            refine ⟨571947294550528256724373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 762596392734037675632497 571947294550528256724373)
            ·
              refine ⟨26810029432056012033955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 571947294550528256724373 26810029432056012033955)
              ·
                rfl

theorem cell19_264325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 6].length) (baseStart_264325 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_264325 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_264325 prefixEnd_264325 := by exact prefixLift 264325
  have htrace : WordTrace (prefixWord ++ tailWord_264325) baseStart_264325 baseEnd_264325 := by
    simpa [prefixWord, tailWord_264325, baseEnd_264325] using wordTrace_append hprefix tailTrace_264325
  have hstable : (prefixWord ++ tailWord_264325).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264325).length < 2 ^ (prefixWord ++ tailWord_264325).sum := by decide
  have hdescent : baseEnd_264325 < baseStart_264325 := by decide
  rcases family_descends (prefixWord ++ tailWord_264325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264380 : List Nat := [2, 2, 2, 3, 3, 2, 5]
def baseStart_264380 : Nat := 118140960795 + 264380 * 2 ^ 59
def prefixEnd_264380 : Nat := 4983230072969 + 3 ^ 40 * 264380 * 2
def baseEnd_264380 : Nat := 26815607987314734959831

theorem tailTrace_264380 : CollatzResearch.WordTrace tailWord_264380 prefixEnd_264380 26815607987314734959831 := by
  unfold tailWord_264380
  simp only [CollatzResearch.WordTrace]
  refine ⟨4821365391101943677167297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6428487188135924902889729 4821365391101943677167297)
  ·
    refine ⟨3616024043326457757875473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4821365391101943677167297 3616024043326457757875473)
    ·
      refine ⟨2712018032494843318406605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3616024043326457757875473 2712018032494843318406605)
      ·
        refine ⟨1017006762185566244402477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2712018032494843318406605 1017006762185566244402477)
        ·
          refine ⟨381377535819587341650929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1017006762185566244402477 381377535819587341650929)
          ·
            refine ⟨286033151864690506238197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381377535819587341650929 286033151864690506238197)
            ·
              refine ⟨26815607987314734959831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 286033151864690506238197 26815607987314734959831)
              ·
                rfl

theorem cell19_264380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 5].length) (baseStart_264380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_264380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_264380 prefixEnd_264380 := by exact prefixLift 264380
  have htrace : WordTrace (prefixWord ++ tailWord_264380) baseStart_264380 baseEnd_264380 := by
    simpa [prefixWord, tailWord_264380, baseEnd_264380] using wordTrace_append hprefix tailTrace_264380
  have hstable : (prefixWord ++ tailWord_264380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264380).length < 2 ^ (prefixWord ++ tailWord_264380).sum := by decide
  have hdescent : baseEnd_264380 < baseStart_264380 := by decide
  rcases family_descends (prefixWord ++ tailWord_264380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264456 : List Nat := [2, 1, 3, 2, 3, 3, 1, 4]
def baseStart_264456 : Nat := 118140960795 + 264456 * 2 ^ 59
def prefixEnd_264456 : Nat := 4983230072969 + 3 ^ 40 * 264456 * 2
def baseEnd_264456 : Nat := 80469949609198547190397

theorem tailTrace_264456 : CollatzResearch.WordTrace tailWord_264456 prefixEnd_264456 80469949609198547190397 := by
  unfold tailWord_264456
  simp only [CollatzResearch.WordTrace]
  refine ⟨4822751364964276167050611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6430335153285701556067481 4822751364964276167050611)
  ·
    refine ⟨7234127047446414250575917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4822751364964276167050611 7234127047446414250575917)
    ·
      refine ⟨2712797642792405343965969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7234127047446414250575917 2712797642792405343965969)
      ·
        refine ⟨2034598232094304007974477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2712797642792405343965969 2034598232094304007974477)
        ·
          refine ⟨762974337035364002990429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2034598232094304007974477 762974337035364002990429)
          ·
            refine ⟨286115376388261501121411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 762974337035364002990429 286115376388261501121411)
            ·
              refine ⟨429173064582392251682117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286115376388261501121411 429173064582392251682117)
              ·
                refine ⟨80469949609198547190397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 429173064582392251682117 80469949609198547190397)
                ·
                  rfl

theorem cell19_264456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_264456 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_264456 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_264456 prefixEnd_264456 := by exact prefixLift 264456
  have htrace : WordTrace (prefixWord ++ tailWord_264456) baseStart_264456 baseEnd_264456 := by
    simpa [prefixWord, tailWord_264456, baseEnd_264456] using wordTrace_append hprefix tailTrace_264456
  have hstable : (prefixWord ++ tailWord_264456).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264456).length < 2 ^ (prefixWord ++ tailWord_264456).sum := by decide
  have hdescent : baseEnd_264456 < baseStart_264456 := by decide
  rcases family_descends (prefixWord ++ tailWord_264456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264458 : List Nat := [3, 1, 2, 2, 1, 1, 5, 4]
def baseStart_264458 : Nat := 118140960795 + 264458 * 2 ^ 59
def prefixEnd_264458 : Nat := 4983230072969 + 3 ^ 40 * 264458 * 2
def baseEnd_264458 : Nat := 80470558178863135145947

theorem tailTrace_264458 : CollatzResearch.WordTrace tailWord_264458 prefixEnd_264458 80470558178863135145947 := by
  unfold tailWord_264458
  simp only [CollatzResearch.WordTrace]
  refine ⟨2411393918980326668918507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6430383783947537783782685 2411393918980326668918507)
  ·
    refine ⟨3617090878470490003377761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2411393918980326668918507 3617090878470490003377761)
    ·
      refine ⟨2712818158852867502533321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3617090878470490003377761 2712818158852867502533321)
      ·
        refine ⟨2034613619139650626899991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2712818158852867502533321 2034613619139650626899991)
        ·
          refine ⟨3051920428709475940349987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2034613619139650626899991 3051920428709475940349987)
          ·
            refine ⟨4577880643064213910524981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051920428709475940349987 4577880643064213910524981)
            ·
              refine ⟨429176310287270054111717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4577880643064213910524981 429176310287270054111717)
              ·
                refine ⟨80470558178863135145947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 429176310287270054111717 80470558178863135145947)
                ·
                  rfl

theorem cell19_264458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_264458 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_264458 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_264458 prefixEnd_264458 := by exact prefixLift 264458
  have htrace : WordTrace (prefixWord ++ tailWord_264458) baseStart_264458 baseEnd_264458 := by
    simpa [prefixWord, tailWord_264458, baseEnd_264458] using wordTrace_append hprefix tailTrace_264458
  have hstable : (prefixWord ++ tailWord_264458).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264458).length < 2 ^ (prefixWord ++ tailWord_264458).sum := by decide
  have hdescent : baseEnd_264458 < baseStart_264458 := by decide
  rcases family_descends (prefixWord ++ tailWord_264458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264532 : List Nat := [2, 4, 1, 1, 2, 2, 4, 3]
def baseStart_264532 : Nat := 118140960795 + 264532 * 2 ^ 59
def prefixEnd_264532 : Nat := 4983230072969 + 3 ^ 40 * 264532 * 2
def baseEnd_264532 : Nat := 80493075256452889501301

theorem tailTrace_264532 : CollatzResearch.WordTrace tailWord_264532 prefixEnd_264532 80493075256452889501301 := by
  unfold tailWord_264532
  simp only [CollatzResearch.WordTrace]
  refine ⟨4824137338826608656933925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6432183118435478209245233 4824137338826608656933925)
  ·
    refine ⟨904525751029989123175111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4824137338826608656933925 904525751029989123175111)
    ·
      refine ⟨1356788626544983684762667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 904525751029989123175111 1356788626544983684762667)
      ·
        refine ⟨2035182939817475527144001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1356788626544983684762667 2035182939817475527144001)
        ·
          refine ⟨1526387204863106645358001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2035182939817475527144001 1526387204863106645358001)
          ·
            refine ⟨1144790403647329984018501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1526387204863106645358001 1144790403647329984018501)
            ·
              refine ⟨214648200683874372003469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1144790403647329984018501 214648200683874372003469)
              ·
                refine ⟨80493075256452889501301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214648200683874372003469 80493075256452889501301)
                ·
                  rfl

theorem cell19_264532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_264532 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_264532 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_264532 prefixEnd_264532 := by exact prefixLift 264532
  have htrace : WordTrace (prefixWord ++ tailWord_264532) baseStart_264532 baseEnd_264532 := by
    simpa [prefixWord, tailWord_264532, baseEnd_264532] using wordTrace_append hprefix tailTrace_264532
  have hstable : (prefixWord ++ tailWord_264532).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264532).length < 2 ^ (prefixWord ++ tailWord_264532).sum := by decide
  have hdescent : baseEnd_264532 < baseStart_264532 := by decide
  rcases family_descends (prefixWord ++ tailWord_264532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264644 : List Nat := [2, 3, 3, 2, 2, 1, 3, 3]
def baseStart_264644 : Nat := 118140960795 + 264644 * 2 ^ 59
def prefixEnd_264644 : Nat := 4983230072969 + 3 ^ 40 * 264644 * 2
def baseEnd_264644 : Nat := 80527155157669815012107

theorem tailTrace_264644 : CollatzResearch.WordTrace tailWord_264644 prefixEnd_264644 80527155157669815012107 := by
  unfold tailWord_264644
  simp only [CollatzResearch.WordTrace]
  refine ⟨4826179826623730220972493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6434906435498306961296657 4826179826623730220972493)
  ·
    refine ⟨1809817434983898832864685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4826179826623730220972493 1809817434983898832864685)
    ·
      refine ⟨678681538118962062324257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1809817434983898832864685 678681538118962062324257)
      ·
        refine ⟨509011153589221546743193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 678681538118962062324257 509011153589221546743193)
        ·
          refine ⟨381758365191916160057395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509011153589221546743193 381758365191916160057395)
          ·
            refine ⟨572637547787874240086093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381758365191916160057395 572637547787874240086093)
            ·
              refine ⟨214739080420452840032285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 572637547787874240086093 214739080420452840032285)
              ·
                refine ⟨80527155157669815012107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214739080420452840032285 80527155157669815012107)
                ·
                  rfl

theorem cell19_264644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_264644 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_264644 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_264644 prefixEnd_264644 := by exact prefixLift 264644
  have htrace : WordTrace (prefixWord ++ tailWord_264644) baseStart_264644 baseEnd_264644 := by
    simpa [prefixWord, tailWord_264644, baseEnd_264644] using wordTrace_append hprefix tailTrace_264644
  have hstable : (prefixWord ++ tailWord_264644).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264644).length < 2 ^ (prefixWord ++ tailWord_264644).sum := by decide
  have hdescent : baseEnd_264644 < baseStart_264644 := by decide
  rcases family_descends (prefixWord ++ tailWord_264644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264688 : List Nat := [2, 1, 1, 1, 3, 3, 2, 6]
def baseStart_264688 : Nat := 118140960795 + 264688 * 2 ^ 59
def prefixEnd_264688 : Nat := 4983230072969 + 3 ^ 40 * 264688 * 2
def baseEnd_264688 : Nat := 80540543690290750034209

theorem tailTrace_264688 : CollatzResearch.WordTrace tailWord_264688 prefixEnd_264688 80540543690290750034209 := by
  unfold tailWord_264688
  simp only [CollatzResearch.WordTrace]
  refine ⟨4826982232544027978273359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6435976310058703971031145 4826982232544027978273359)
  ·
    refine ⟨7240473348816041967410039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4826982232544027978273359 7240473348816041967410039)
    ·
      refine ⟨10860710023224062951115059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7240473348816041967410039 10860710023224062951115059)
      ·
        refine ⟨16291065034836094426672589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10860710023224062951115059 16291065034836094426672589)
        ·
          refine ⟨6109149388063535410002221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16291065034836094426672589 6109149388063535410002221)
          ·
            refine ⟨2290931020523825778750833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6109149388063535410002221 2290931020523825778750833)
            ·
              refine ⟨1718198265392869334063125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2290931020523825778750833 1718198265392869334063125)
              ·
                refine ⟨80540543690290750034209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1718198265392869334063125 80540543690290750034209)
                ·
                  rfl

theorem cell19_264688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_264688 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_264688 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_264688 prefixEnd_264688 := by exact prefixLift 264688
  have htrace : WordTrace (prefixWord ++ tailWord_264688) baseStart_264688 baseEnd_264688 := by
    simpa [prefixWord, tailWord_264688, baseEnd_264688] using wordTrace_append hprefix tailTrace_264688
  have hstable : (prefixWord ++ tailWord_264688).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264688).length < 2 ^ (prefixWord ++ tailWord_264688).sum := by decide
  have hdescent : baseEnd_264688 < baseStart_264688 := by decide
  rcases family_descends (prefixWord ++ tailWord_264688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264705 : List Nat := [1, 2, 4, 1, 3, 2, 1, 5]
def baseStart_264705 : Nat := 118140960795 + 264705 * 2 ^ 59
def prefixEnd_264705 : Nat := 4983230072969 + 3 ^ 40 * 264705 * 2
def baseEnd_264705 : Nat := 80545716532439747656385

theorem tailTrace_264705 : CollatzResearch.WordTrace tailWord_264705 prefixEnd_264705 80545716532439747656385 := by
  unfold tailWord_264705
  simp only [CollatzResearch.WordTrace]
  refine ⟨9654584506026467859915569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6436389670684311906610379 9654584506026467859915569)
  ·
    refine ⟨7240938379519850894936677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9654584506026467859915569 7240938379519850894936677)
    ·
      refine ⟨1357675946159972042800627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7240938379519850894936677 1357675946159972042800627)
      ·
        refine ⟨2036513919239958064200941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1357675946159972042800627 2036513919239958064200941)
        ·
          refine ⟨763692719714984274075353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2036513919239958064200941 763692719714984274075353)
          ·
            refine ⟨572769539786238205556515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 763692719714984274075353 572769539786238205556515)
            ·
              refine ⟨859154309679357308334773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572769539786238205556515 859154309679357308334773)
              ·
                refine ⟨80545716532439747656385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 859154309679357308334773 80545716532439747656385)
                ·
                  rfl

theorem cell19_264705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_264705 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_264705 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_264705 prefixEnd_264705 := by exact prefixLift 264705
  have htrace : WordTrace (prefixWord ++ tailWord_264705) baseStart_264705 baseEnd_264705 := by
    simpa [prefixWord, tailWord_264705, baseEnd_264705] using wordTrace_append hprefix tailTrace_264705
  have hstable : (prefixWord ++ tailWord_264705).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264705).length < 2 ^ (prefixWord ++ tailWord_264705).sum := by decide
  have hdescent : baseEnd_264705 < baseStart_264705 := by decide
  rcases family_descends (prefixWord ++ tailWord_264705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264707 : List Nat := [1, 1, 1, 3, 2, 1, 5, 5]
def baseStart_264707 : Nat := 118140960795 + 264707 * 2 ^ 59
def prefixEnd_264707 : Nat := 4983230072969 + 3 ^ 40 * 264707 * 2
def baseEnd_264707 : Nat := 80546325102104335611935

theorem tailTrace_264707 : CollatzResearch.WordTrace tailWord_264707 prefixEnd_264707 80546325102104335611935 := by
  unfold tailWord_264707
  simp only [CollatzResearch.WordTrace]
  refine ⟨9654657452019222201488375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6436438301346148134325583 9654657452019222201488375)
  ·
    refine ⟨14481986178028833302232563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9654657452019222201488375 14481986178028833302232563)
    ·
      refine ⟨21722979267043249953348845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14481986178028833302232563 21722979267043249953348845)
      ·
        refine ⟨8146117225141218732505817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21722979267043249953348845 8146117225141218732505817)
        ·
          refine ⟨6109587918855914049379363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8146117225141218732505817 6109587918855914049379363)
          ·
            refine ⟨9164381878283871074069045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6109587918855914049379363 9164381878283871074069045)
            ·
              refine ⟨859160801089112913193973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9164381878283871074069045 859160801089112913193973)
              ·
                refine ⟨80546325102104335611935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 859160801089112913193973 80546325102104335611935)
                ·
                  rfl

theorem cell19_264707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_264707 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_264707 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_264707 prefixEnd_264707 := by exact prefixLift 264707
  have htrace : WordTrace (prefixWord ++ tailWord_264707) baseStart_264707 baseEnd_264707 := by
    simpa [prefixWord, tailWord_264707, baseEnd_264707] using wordTrace_append hprefix tailTrace_264707
  have hstable : (prefixWord ++ tailWord_264707).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264707).length < 2 ^ (prefixWord ++ tailWord_264707).sum := by decide
  have hdescent : baseEnd_264707 < baseStart_264707 := by decide
  rcases family_descends (prefixWord ++ tailWord_264707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264781 : List Nat := [1, 6, 1, 1, 2, 8]
def baseStart_264781 : Nat := 118140960795 + 264781 * 2 ^ 59
def prefixEnd_264781 : Nat := 4983230072969 + 3 ^ 40 * 264781 * 2
def baseEnd_264781 : Nat := 8952093575521565551921

theorem tailTrace_264781 : CollatzResearch.WordTrace tailWord_264781 prefixEnd_264781 8952093575521565551921 := by
  unfold tailWord_264781
  simp only [CollatzResearch.WordTrace]
  refine ⟨9657356453751132839682197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6438237635834088559788131 9657356453751132839682197)
  ·
    refine ⟨452688583769584351860103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9657356453751132839682197 452688583769584351860103)
    ·
      refine ⟨679032875654376527790155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452688583769584351860103 679032875654376527790155)
      ·
        refine ⟨1018549313481564791685233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679032875654376527790155 1018549313481564791685233)
        ·
          refine ⟨763911985111173593763925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1018549313481564791685233 763911985111173593763925)
          ·
            refine ⟨8952093575521565551921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 763911985111173593763925 8952093575521565551921)
            ·
              rfl

theorem cell19_264781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 8].length) (baseStart_264781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_264781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_264781 prefixEnd_264781 := by exact prefixLift 264781
  have htrace : WordTrace (prefixWord ++ tailWord_264781) baseStart_264781 baseEnd_264781 := by
    simpa [prefixWord, tailWord_264781, baseEnd_264781] using wordTrace_append hprefix tailTrace_264781
  have hstable : (prefixWord ++ tailWord_264781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264781).length < 2 ^ (prefixWord ++ tailWord_264781).sum := by decide
  have hdescent : baseEnd_264781 < baseStart_264781 := by decide
  rcases family_descends (prefixWord ++ tailWord_264781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264796 : List Nat := [2, 2, 4, 1, 4, 1, 1, 4]
def baseStart_264796 : Nat := 118140960795 + 264796 * 2 ^ 59
def prefixEnd_264796 : Nat := 4983230072969 + 3 ^ 40 * 264796 * 2
def baseEnd_264796 : Nat := 80573406452178499633915

theorem tailTrace_264796 : CollatzResearch.WordTrace tailWord_264796 prefixEnd_264796 80573406452178499633915 := by
  unfold tailWord_264796
  simp only [CollatzResearch.WordTrace]
  refine ⟨4828951774348395200739121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6438602365797860267652161 4828951774348395200739121)
  ·
    refine ⟨3621713830761296400554341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4828951774348395200739121 3621713830761296400554341)
    ·
      refine ⟨679071343267743075103939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3621713830761296400554341 679071343267743075103939)
      ·
        refine ⟨1018607014901614612655909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679071343267743075103939 1018607014901614612655909)
        ·
          refine ⟨190988815294052739872983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1018607014901614612655909 190988815294052739872983)
          ·
            refine ⟨286483222941079109809475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190988815294052739872983 286483222941079109809475)
            ·
              refine ⟨429724834411618664714213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286483222941079109809475 429724834411618664714213)
              ·
                refine ⟨80573406452178499633915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 429724834411618664714213 80573406452178499633915)
                ·
                  rfl

theorem cell19_264796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 4].length) (baseStart_264796 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_264796 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_264796 prefixEnd_264796 := by exact prefixLift 264796
  have htrace : WordTrace (prefixWord ++ tailWord_264796) baseStart_264796 baseEnd_264796 := by
    simpa [prefixWord, tailWord_264796, baseEnd_264796] using wordTrace_append hprefix tailTrace_264796
  have hstable : (prefixWord ++ tailWord_264796).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264796).length < 2 ^ (prefixWord ++ tailWord_264796).sum := by decide
  have hdescent : baseEnd_264796 < baseStart_264796 := by decide
  rcases family_descends (prefixWord ++ tailWord_264796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264948 : List Nat := [2, 6, 1, 1, 3, 6]
def baseStart_264948 : Nat := 118140960795 + 264948 * 2 ^ 59
def prefixEnd_264948 : Nat := 4983230072969 + 3 ^ 40 * 264948 * 2
def baseEnd_264948 : Nat := 8957739749631909361747

theorem tailTrace_264948 : CollatzResearch.WordTrace tailWord_264948 prefixEnd_264948 8957739749631909361747 := by
  unfold tailWord_264948
  simp only [CollatzResearch.WordTrace]
  refine ⟨4831723722073060180505749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6442298296097413574007665 4831723722073060180505749)
  ·
    refine ⟨226487049472174695961207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4831723722073060180505749 226487049472174695961207)
    ·
      refine ⟨339730574208262043941811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226487049472174695961207 339730574208262043941811)
      ·
        refine ⟨509595861312393065912717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339730574208262043941811 509595861312393065912717)
        ·
          refine ⟨191098447992147399717269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 509595861312393065912717 191098447992147399717269)
          ·
            refine ⟨8957739749631909361747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 191098447992147399717269 8957739749631909361747)
            ·
              rfl

theorem cell19_264948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 6].length) (baseStart_264948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_264948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_264948 prefixEnd_264948 := by exact prefixLift 264948
  have htrace : WordTrace (prefixWord ++ tailWord_264948) baseStart_264948 baseEnd_264948 := by
    simpa [prefixWord, tailWord_264948, baseEnd_264948] using wordTrace_append hprefix tailTrace_264948
  have hstable : (prefixWord ++ tailWord_264948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264948).length < 2 ^ (prefixWord ++ tailWord_264948).sum := by decide
  have hdescent : baseEnd_264948 < baseStart_264948 := by decide
  rcases family_descends (prefixWord ++ tailWord_264948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265011 : List Nat := [1, 1, 1, 2, 6, 2, 6]
def baseStart_265011 : Nat := 118140960795 + 265011 * 2 ^ 59
def prefixEnd_265011 : Nat := 4983230072969 + 3 ^ 40 * 265011 * 2
def baseEnd_265011 : Nat := 26879609230373901618517

theorem tailTrace_265011 : CollatzResearch.WordTrace tailWord_265011 prefixEnd_265011 26879609230373901618517 := by
  unfold tailWord_265011
  simp only [CollatzResearch.WordTrace]
  refine ⟨9665745242917882120554887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6443830161945254747036591 9665745242917882120554887)
  ·
    refine ⟨14498617864376823180832331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9665745242917882120554887 14498617864376823180832331)
    ·
      refine ⟨21747926796565234771248497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14498617864376823180832331 21747926796565234771248497)
      ·
        refine ⟨16310945097423926078436373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21747926796565234771248497 16310945097423926078436373)
        ·
          refine ⟨764575551441746534926705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16310945097423926078436373 764575551441746534926705)
          ·
            refine ⟨573431663581309901195029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764575551441746534926705 573431663581309901195029)
            ·
              refine ⟨26879609230373901618517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 573431663581309901195029 26879609230373901618517)
              ·
                rfl

theorem cell19_265011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 6].length) (baseStart_265011 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265011 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265011 prefixEnd_265011 := by exact prefixLift 265011
  have htrace : WordTrace (prefixWord ++ tailWord_265011) baseStart_265011 baseEnd_265011 := by
    simpa [prefixWord, tailWord_265011, baseEnd_265011] using wordTrace_append hprefix tailTrace_265011
  have hstable : (prefixWord ++ tailWord_265011).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265011).length < 2 ^ (prefixWord ++ tailWord_265011).sum := by decide
  have hdescent : baseEnd_265011 < baseStart_265011 := by decide
  rcases family_descends (prefixWord ++ tailWord_265011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265047 : List Nat := [1, 1, 3, 2, 4, 1, 4, 3]
def baseStart_265047 : Nat := 118140960795 + 265047 * 2 ^ 59
def prefixEnd_265047 : Nat := 4983230072969 + 3 ^ 40 * 265047 * 2
def baseEnd_265047 : Nat := 80649781945084288055453

theorem tailTrace_265047 : CollatzResearch.WordTrace tailWord_265047 prefixEnd_265047 80649781945084288055453 := by
  unfold tailWord_265047
  simp only [CollatzResearch.WordTrace]
  refine ⟨9667058270787460268865395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6444705513858306845910263 9667058270787460268865395)
  ·
    refine ⟨14500587406181190403298093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9667058270787460268865395 14500587406181190403298093)
    ·
      refine ⟨5437720277317946401236785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14500587406181190403298093 5437720277317946401236785)
      ·
        refine ⟨4078290207988459800927589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5437720277317946401236785 4078290207988459800927589)
        ·
          refine ⟨764679413997836212673923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4078290207988459800927589 764679413997836212673923)
          ·
            refine ⟨1147019120996754319010885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764679413997836212673923 1147019120996754319010885)
            ·
              refine ⟨215066085186891434814541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1147019120996754319010885 215066085186891434814541)
              ·
                refine ⟨80649781945084288055453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215066085186891434814541 80649781945084288055453)
                ·
                  rfl

theorem cell19_265047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 3].length) (baseStart_265047 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265047 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265047 prefixEnd_265047 := by exact prefixLift 265047
  have htrace : WordTrace (prefixWord ++ tailWord_265047) baseStart_265047 baseEnd_265047 := by
    simpa [prefixWord, tailWord_265047, baseEnd_265047] using wordTrace_append hprefix tailTrace_265047
  have hstable : (prefixWord ++ tailWord_265047).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265047).length < 2 ^ (prefixWord ++ tailWord_265047).sum := by decide
  have hdescent : baseEnd_265047 < baseStart_265047 := by decide
  rcases family_descends (prefixWord ++ tailWord_265047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265049 : List Nat := [1, 2, 1, 2, 2, 5, 1, 5]
def baseStart_265049 : Nat := 118140960795 + 265049 * 2 ^ 59
def prefixEnd_265049 : Nat := 4983230072969 + 3 ^ 40 * 265049 * 2
def baseEnd_265049 : Nat := 80650390514748876011003

theorem tailTrace_265049 : CollatzResearch.WordTrace tailWord_265049 prefixEnd_265049 80650390514748876011003 := by
  unfold tailWord_265049
  simp only [CollatzResearch.WordTrace]
  refine ⟨9667131216780214610438201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6444754144520143073625467 9667131216780214610438201)
  ·
    refine ⟨7250348412585160957828651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9667131216780214610438201 7250348412585160957828651)
    ·
      refine ⟨10875522618877741436742977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7250348412585160957828651 10875522618877741436742977)
      ·
        refine ⟨8156641964158306077557233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10875522618877741436742977 8156641964158306077557233)
        ·
          refine ⟨6117481473118729558167925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8156641964158306077557233 6117481473118729558167925)
          ·
            refine ⟨573513888104880896078243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6117481473118729558167925 573513888104880896078243)
            ·
              refine ⟨860270832157321344117365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573513888104880896078243 860270832157321344117365)
              ·
                refine ⟨80650390514748876011003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 860270832157321344117365 80650390514748876011003)
                ·
                  rfl

theorem cell19_265049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_265049 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265049 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265049 prefixEnd_265049 := by exact prefixLift 265049
  have htrace : WordTrace (prefixWord ++ tailWord_265049) baseStart_265049 baseEnd_265049 := by
    simpa [prefixWord, tailWord_265049, baseEnd_265049] using wordTrace_append hprefix tailTrace_265049
  have hstable : (prefixWord ++ tailWord_265049).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265049).length < 2 ^ (prefixWord ++ tailWord_265049).sum := by decide
  have hdescent : baseEnd_265049 < baseStart_265049 := by decide
  rcases family_descends (prefixWord ++ tailWord_265049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265140 : List Nat := [2, 5, 2, 1, 1, 1, 3, 4]
def baseStart_265140 : Nat := 118140960795 + 265140 * 2 ^ 59
def prefixEnd_265140 : Nat := 4983230072969 + 3 ^ 40 * 265140 * 2
def baseEnd_265140 : Nat := 80678080434487627988533

theorem tailTrace_265140 : CollatzResearch.WordTrace tailWord_265140 prefixEnd_265140 80678080434487627988533 := by
  unfold tailWord_265140
  simp only [CollatzResearch.WordTrace]
  refine ⟨4835225129725268576000437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6446966839633691434667249 4835225129725268576000437)
  ·
    refine ⟨453302355911743929000041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4835225129725268576000437 453302355911743929000041)
    ·
      refine ⟨339976766933807946750031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453302355911743929000041 339976766933807946750031)
      ·
        refine ⟨509965150400711920125047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339976766933807946750031 509965150400711920125047)
        ·
          refine ⟨764947725601067880187571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509965150400711920125047 764947725601067880187571)
          ·
            refine ⟨1147421588401601820281357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764947725601067880187571 1147421588401601820281357)
            ·
              refine ⟨430283095650600682605509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1147421588401601820281357 430283095650600682605509)
              ·
                refine ⟨80678080434487627988533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 430283095650600682605509 80678080434487627988533)
                ·
                  rfl

theorem cell19_265140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_265140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265140 prefixEnd_265140 := by exact prefixLift 265140
  have htrace : WordTrace (prefixWord ++ tailWord_265140) baseStart_265140 baseEnd_265140 := by
    simpa [prefixWord, tailWord_265140, baseEnd_265140] using wordTrace_append hprefix tailTrace_265140
  have hstable : (prefixWord ++ tailWord_265140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265140).length < 2 ^ (prefixWord ++ tailWord_265140).sum := by decide
  have hdescent : baseEnd_265140 < baseStart_265140 := by decide
  rcases family_descends (prefixWord ++ tailWord_265140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265144 : List Nat := [2, 1, 2, 1, 2, 4, 3, 4]
def baseStart_265144 : Nat := 118140960795 + 265144 * 2 ^ 59
def prefixEnd_265144 : Nat := 4983230072969 + 3 ^ 40 * 265144 * 2
def baseEnd_265144 : Nat := 80679297573816803899633

theorem tailTrace_265144 : CollatzResearch.WordTrace tailWord_265144 prefixEnd_265144 80679297573816803899633 := by
  unfold tailWord_265144
  simp only [CollatzResearch.WordTrace]
  refine ⟨4835298075718022917573243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6447064100957363890097657 4835298075718022917573243)
  ·
    refine ⟨7252947113577034376359865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4835298075718022917573243 7252947113577034376359865)
    ·
      refine ⟨5439710335182775782269899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7252947113577034376359865 5439710335182775782269899)
      ·
        refine ⟨8159565502774163673404849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5439710335182775782269899 8159565502774163673404849)
        ·
          refine ⟨6119674127080622755053637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8159565502774163673404849 6119674127080622755053637)
          ·
            refine ⟨1147438898827616766572557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6119674127080622755053637 1147438898827616766572557)
            ·
              refine ⟨430289587060356287464709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1147438898827616766572557 430289587060356287464709)
              ·
                refine ⟨80679297573816803899633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 430289587060356287464709 80679297573816803899633)
                ·
                  rfl

theorem cell19_265144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_265144 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265144 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265144 prefixEnd_265144 := by exact prefixLift 265144
  have htrace : WordTrace (prefixWord ++ tailWord_265144) baseStart_265144 baseEnd_265144 := by
    simpa [prefixWord, tailWord_265144, baseEnd_265144] using wordTrace_append hprefix tailTrace_265144
  have hstable : (prefixWord ++ tailWord_265144).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265144).length < 2 ^ (prefixWord ++ tailWord_265144).sum := by decide
  have hdescent : baseEnd_265144 < baseStart_265144 := by decide
  rcases family_descends (prefixWord ++ tailWord_265144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265214 : List Nat := [4, 2, 2, 2, 2, 2, 2, 3]
def baseStart_265214 : Nat := 118140960795 + 265214 * 2 ^ 59
def prefixEnd_265214 : Nat := 4983230072969 + 3 ^ 40 * 265214 * 2
def baseEnd_265214 : Nat := 80700597512077382343887

theorem tailTrace_265214 : CollatzResearch.WordTrace tailWord_265214 prefixEnd_265214 80700597512077382343887 := by
  unfold tailWord_265214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1209143657647805973774337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6448766174121631860129797 1209143657647805973774337)
  ·
    refine ⟨906857743235854480330753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1209143657647805973774337 906857743235854480330753)
    ·
      refine ⟨680143307426890860248065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 906857743235854480330753 680143307426890860248065)
      ·
        refine ⟨510107480570168145186049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680143307426890860248065 510107480570168145186049)
        ·
          refine ⟨382580610427626108889537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510107480570168145186049 382580610427626108889537)
          ·
            refine ⟨286935457820719581667153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382580610427626108889537 286935457820719581667153)
            ·
              refine ⟨215201593365539686250365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286935457820719581667153 215201593365539686250365)
              ·
                refine ⟨80700597512077382343887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215201593365539686250365 80700597512077382343887)
                ·
                  rfl

theorem cell19_265214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_265214 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265214 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265214 prefixEnd_265214 := by exact prefixLift 265214
  have htrace : WordTrace (prefixWord ++ tailWord_265214) baseStart_265214 baseEnd_265214 := by
    simpa [prefixWord, tailWord_265214, baseEnd_265214] using wordTrace_append hprefix tailTrace_265214
  have hstable : (prefixWord ++ tailWord_265214).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265214).length < 2 ^ (prefixWord ++ tailWord_265214).sum := by decide
  have hdescent : baseEnd_265214 < baseStart_265214 := by decide
  rcases family_descends (prefixWord ++ tailWord_265214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265239 : List Nat := [1, 1, 3, 5, 1, 1, 7]
def baseStart_265239 : Nat := 118140960795 + 265239 * 2 ^ 59
def prefixEnd_265239 : Nat := 4983230072969 + 3 ^ 40 * 265239 * 2
def baseEnd_265239 : Nat := 26902734877628243929421

theorem tailTrace_265239 : CollatzResearch.WordTrace tailWord_265239 prefixEnd_265239 26902734877628243929421 := by
  unfold tailWord_265239
  simp only [CollatzResearch.WordTrace]
  refine ⟨9674061086091877059854771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6449374057394584706569847 9674061086091877059854771)
  ·
    refine ⟨14511091629137815589782157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9674061086091877059854771 14511091629137815589782157)
    ·
      refine ⟨5441659360926680846168309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14511091629137815589782157 5441659360926680846168309)
      ·
        refine ⟨510155565086876329328279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5441659360926680846168309 510155565086876329328279)
        ·
          refine ⟨765233347630314493992419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510155565086876329328279 765233347630314493992419)
          ·
            refine ⟨1147850021445471740988629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765233347630314493992419 1147850021445471740988629)
            ·
              refine ⟨26902734877628243929421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1147850021445471740988629 26902734877628243929421)
              ·
                rfl

theorem cell19_265239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 7].length) (baseStart_265239 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265239 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265239 prefixEnd_265239 := by exact prefixLift 265239
  have htrace : WordTrace (prefixWord ++ tailWord_265239) baseStart_265239 baseEnd_265239 := by
    simpa [prefixWord, tailWord_265239, baseEnd_265239] using wordTrace_append hprefix tailTrace_265239
  have hstable : (prefixWord ++ tailWord_265239).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265239).length < 2 ^ (prefixWord ++ tailWord_265239).sum := by decide
  have hdescent : baseEnd_265239 < baseStart_265239 := by decide
  rcases family_descends (prefixWord ++ tailWord_265239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265241 : List Nat := [1, 2, 1, 2, 1, 1, 11]
def baseStart_265241 : Nat := 118140960795 + 265241 * 2 ^ 59
def prefixEnd_265241 : Nat := 4983230072969 + 3 ^ 40 * 265241 * 2
def baseEnd_265241 : Nat := 26902937734183106581271

theorem tailTrace_265241 : CollatzResearch.WordTrace tailWord_265241 prefixEnd_265241 26902937734183106581271 := by
  unfold tailWord_265241
  simp only [CollatzResearch.WordTrace]
  refine ⟨9674134032084631401427577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6449422688056420934285051 9674134032084631401427577)
  ·
    refine ⟨7255600524063473551070683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9674134032084631401427577 7255600524063473551070683)
    ·
      refine ⟨10883400786095210326606025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7255600524063473551070683 10883400786095210326606025)
      ·
        refine ⟨8162550589571407744954519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10883400786095210326606025 8162550589571407744954519)
        ·
          refine ⟨12243825884357111617431779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8162550589571407744954519 12243825884357111617431779)
          ·
            refine ⟨18365738826535667426147669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12243825884357111617431779 18365738826535667426147669)
            ·
              refine ⟨26902937734183106581271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18365738826535667426147669 26902937734183106581271)
              ·
                rfl

theorem cell19_265241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 11].length) (baseStart_265241 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265241 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265241 prefixEnd_265241 := by exact prefixLift 265241
  have htrace : WordTrace (prefixWord ++ tailWord_265241) baseStart_265241 baseEnd_265241 := by
    simpa [prefixWord, tailWord_265241, baseEnd_265241] using wordTrace_append hprefix tailTrace_265241
  have hstable : (prefixWord ++ tailWord_265241).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265241).length < 2 ^ (prefixWord ++ tailWord_265241).sum := by decide
  have hdescent : baseEnd_265241 < baseStart_265241 := by decide
  rcases family_descends (prefixWord ++ tailWord_265241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265277 : List Nat := [1, 4, 1, 3, 1, 2, 2, 5]
def baseStart_265277 : Nat := 118140960795 + 265277 * 2 ^ 59
def prefixEnd_265277 : Nat := 4983230072969 + 3 ^ 40 * 265277 * 2
def baseEnd_265277 : Nat := 80719767456511902943715

theorem tailTrace_265277 : CollatzResearch.WordTrace tailWord_265277 prefixEnd_265277 80719767456511902943715 := by
  unfold tailWord_265277
  simp only [CollatzResearch.WordTrace]
  refine ⟨9675447059954209549738085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6450298039969473033158723 9675447059954209549738085)
  ·
    refine ⟨1814146323741414290575891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9675447059954209549738085 1814146323741414290575891)
    ·
      refine ⟨2721219485612121435863837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1814146323741414290575891 2721219485612121435863837)
      ·
        refine ⟨1020457307104545538448939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2721219485612121435863837 1020457307104545538448939)
        ·
          refine ⟨1530685960656818307673409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020457307104545538448939 1530685960656818307673409)
          ·
            refine ⟨1148014470492613730755057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1530685960656818307673409 1148014470492613730755057)
            ·
              refine ⟨861010852869460298066293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1148014470492613730755057 861010852869460298066293)
              ·
                refine ⟨80719767456511902943715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 861010852869460298066293 80719767456511902943715)
                ·
                  rfl

theorem cell19_265277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_265277 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265277 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265277 prefixEnd_265277 := by exact prefixLift 265277
  have htrace : WordTrace (prefixWord ++ tailWord_265277) baseStart_265277 baseEnd_265277 := by
    simpa [prefixWord, tailWord_265277, baseEnd_265277] using wordTrace_append hprefix tailTrace_265277
  have hstable : (prefixWord ++ tailWord_265277).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265277).length < 2 ^ (prefixWord ++ tailWord_265277).sum := by decide
  have hdescent : baseEnd_265277 < baseStart_265277 := by decide
  rcases family_descends (prefixWord ++ tailWord_265277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265309 : List Nat := [1, 4, 4, 1, 3, 1, 1, 4]
def baseStart_265309 : Nat := 118140960795 + 265309 * 2 ^ 59
def prefixEnd_265309 : Nat := 4983230072969 + 3 ^ 40 * 265309 * 2
def baseEnd_265309 : Nat := 80729504571145310232517

theorem tailTrace_265309 : CollatzResearch.WordTrace tailWord_265309 prefixEnd_265309 80729504571145310232517 := by
  unfold tailWord_265309
  simp only [CollatzResearch.WordTrace]
  refine ⟨9676614195838279014902981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6451076130558852676601987 9676614195838279014902981)
  ·
    refine ⟨1814365161719677315294309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9676614195838279014902981 1814365161719677315294309)
    ·
      refine ⟨340193467822439496617683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1814365161719677315294309 340193467822439496617683)
      ·
        refine ⟨510290201733659244926525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340193467822439496617683 510290201733659244926525)
        ·
          refine ⟨191358825650122216847447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 510290201733659244926525 191358825650122216847447)
          ·
            refine ⟨287038238475183325271171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191358825650122216847447 287038238475183325271171)
            ·
              refine ⟨430557357712774987906757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287038238475183325271171 430557357712774987906757)
              ·
                refine ⟨80729504571145310232517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 430557357712774987906757 80729504571145310232517)
                ·
                  rfl

theorem cell19_265309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 4].length) (baseStart_265309 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265309 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265309 prefixEnd_265309 := by exact prefixLift 265309
  have htrace : WordTrace (prefixWord ++ tailWord_265309) baseStart_265309 baseEnd_265309 := by
    simpa [prefixWord, tailWord_265309, baseEnd_265309] using wordTrace_append hprefix tailTrace_265309
  have hstable : (prefixWord ++ tailWord_265309).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265309).length < 2 ^ (prefixWord ++ tailWord_265309).sum := by decide
  have hdescent : baseEnd_265309 < baseStart_265309 := by decide
  rcases family_descends (prefixWord ++ tailWord_265309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265336 : List Nat := [2, 1, 2, 1, 1, 1, 4, 7]
def baseStart_265336 : Nat := 118140960795 + 265336 * 2 ^ 59
def prefixEnd_265336 : Nat := 4983230072969 + 3 ^ 40 * 265336 * 2
def baseEnd_265336 : Nat := 80737720261617247632443

theorem tailTrace_265336 : CollatzResearch.WordTrace tailWord_265336 prefixEnd_265336 80737720261617247632443 := by
  unfold tailWord_265336
  simp only [CollatzResearch.WordTrace]
  refine ⟨4838799483370231313067931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6451732644493641750757241 4838799483370231313067931)
  ·
    refine ⟨7258199225055346969601897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4838799483370231313067931 7258199225055346969601897)
    ·
      refine ⟨5443649418791510227201423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7258199225055346969601897 5443649418791510227201423)
      ·
        refine ⟨8165474128187265340802135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5443649418791510227201423 8165474128187265340802135)
        ·
          refine ⟨12248211192280898011203203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8165474128187265340802135 12248211192280898011203203)
          ·
            refine ⟨18372316788421347016804805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12248211192280898011203203 18372316788421347016804805)
            ·
              refine ⟨3444809397829002565650901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18372316788421347016804805 3444809397829002565650901)
              ·
                refine ⟨80737720261617247632443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3444809397829002565650901 80737720261617247632443)
                ·
                  rfl

theorem cell19_265336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_265336 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265336 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265336 prefixEnd_265336 := by exact prefixLift 265336
  have htrace : WordTrace (prefixWord ++ tailWord_265336) baseStart_265336 baseEnd_265336 := by
    simpa [prefixWord, tailWord_265336, baseEnd_265336] using wordTrace_append hprefix tailTrace_265336
  have hstable : (prefixWord ++ tailWord_265336).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265336).length < 2 ^ (prefixWord ++ tailWord_265336).sum := by decide
  have hdescent : baseEnd_265336 < baseStart_265336 := by decide
  rcases family_descends (prefixWord ++ tailWord_265336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265389 : List Nat := [1, 5, 2, 1, 3, 1, 1, 5]
def baseStart_265389 : Nat := 118140960795 + 265389 * 2 ^ 59
def prefixEnd_265389 : Nat := 4983230072969 + 3 ^ 40 * 265389 * 2
def baseEnd_265389 : Nat := 80753847357728828454521

theorem tailTrace_265389 : CollatzResearch.WordTrace tailWord_265389 prefixEnd_265389 80753847357728828454521 := by
  unfold tailWord_265389
  simp only [CollatzResearch.WordTrace]
  refine ⟨9679532035548452677815221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6453021357032301785210147 9679532035548452677815221)
  ·
    refine ⟨907456128332667438545177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9679532035548452677815221 907456128332667438545177)
    ·
      refine ⟨680592096249500578908883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 907456128332667438545177 680592096249500578908883)
      ·
        refine ⟨1020888144374250868363325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680592096249500578908883 1020888144374250868363325)
        ·
          refine ⟨382833054140344075636247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1020888144374250868363325 382833054140344075636247)
          ·
            refine ⟨574249581210516113454371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382833054140344075636247 574249581210516113454371)
            ·
              refine ⟨861374371815774170181557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574249581210516113454371 861374371815774170181557)
              ·
                refine ⟨80753847357728828454521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 861374371815774170181557 80753847357728828454521)
                ·
                  rfl

theorem cell19_265389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 5].length) (baseStart_265389 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265389 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265389 prefixEnd_265389 := by exact prefixLift 265389
  have htrace : WordTrace (prefixWord ++ tailWord_265389) baseStart_265389 baseEnd_265389 := by
    simpa [prefixWord, tailWord_265389, baseEnd_265389] using wordTrace_append hprefix tailTrace_265389
  have hstable : (prefixWord ++ tailWord_265389).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265389).length < 2 ^ (prefixWord ++ tailWord_265389).sum := by decide
  have hdescent : baseEnd_265389 < baseStart_265389 := by decide
  rcases family_descends (prefixWord ++ tailWord_265389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265391 : List Nat := [1, 1, 2, 1, 2, 3, 6, 3]
def baseStart_265391 : Nat := 118140960795 + 265391 * 2 ^ 59
def prefixEnd_265391 : Nat := 4983230072969 + 3 ^ 40 * 265391 * 2
def baseEnd_265391 : Nat := 80754455927393416410071

theorem tailTrace_265391 : CollatzResearch.WordTrace tailWord_265391 prefixEnd_265391 80754455927393416410071 := by
  unfold tailWord_265391
  simp only [CollatzResearch.WordTrace]
  refine ⟨9679604981541207019388027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6453069987694138012925351 9679604981541207019388027)
  ·
    refine ⟨14519407472311810529082041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9679604981541207019388027 14519407472311810529082041)
    ·
      refine ⟨10889555604233857896811531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14519407472311810529082041 10889555604233857896811531)
      ·
        refine ⟨16334333406350786845217297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10889555604233857896811531 16334333406350786845217297)
        ·
          refine ⟨12250750054763090133912973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16334333406350786845217297 12250750054763090133912973)
          ·
            refine ⟨4594031270536158800217365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12250750054763090133912973 4594031270536158800217365)
            ·
              refine ⟨215345215806382443760189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4594031270536158800217365 215345215806382443760189)
              ·
                refine ⟨80754455927393416410071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215345215806382443760189 80754455927393416410071)
                ·
                  rfl

theorem cell19_265391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 3].length) (baseStart_265391 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265391 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265391 prefixEnd_265391 := by exact prefixLift 265391
  have htrace : WordTrace (prefixWord ++ tailWord_265391) baseStart_265391 baseEnd_265391 := by
    simpa [prefixWord, tailWord_265391, baseEnd_265391] using wordTrace_append hprefix tailTrace_265391
  have hstable : (prefixWord ++ tailWord_265391).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265391).length < 2 ^ (prefixWord ++ tailWord_265391).sum := by decide
  have hdescent : baseEnd_265391 < baseStart_265391 := by decide
  rcases family_descends (prefixWord ++ tailWord_265391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265408 : List Nat := [2, 1, 1, 2, 7, 1, 5]
def baseStart_265408 : Nat := 118140960795 + 265408 * 2 ^ 59
def prefixEnd_265408 : Nat := 4983230072969 + 3 ^ 40 * 265408 * 2
def baseEnd_265408 : Nat := 26919876256514138010749

theorem tailTrace_265408 : CollatzResearch.WordTrace tailWord_265408 prefixEnd_265408 26919876256514138010749 := by
  unfold tailWord_265408
  simp only [CollatzResearch.WordTrace]
  refine ⟨4840112511239809461378439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6453483348319745948504585 4840112511239809461378439)
  ·
    refine ⟨7260168766859714192067659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4840112511239809461378439 7260168766859714192067659)
    ·
      refine ⟨10890253150289571288101489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7260168766859714192067659 10890253150289571288101489)
      ·
        refine ⟨8167689862717178466076117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10890253150289571288101489 8167689862717178466076117)
        ·
          refine ⟨191430231157433870298659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 8167689862717178466076117 191430231157433870298659)
          ·
            refine ⟨287145346736150805447989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191430231157433870298659 287145346736150805447989)
            ·
              refine ⟨26919876256514138010749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287145346736150805447989 26919876256514138010749)
              ·
                rfl

theorem cell19_265408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 5].length) (baseStart_265408 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265408 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265408 prefixEnd_265408 := by exact prefixLift 265408
  have htrace : WordTrace (prefixWord ++ tailWord_265408) baseStart_265408 baseEnd_265408 := by
    simpa [prefixWord, tailWord_265408, baseEnd_265408] using wordTrace_append hprefix tailTrace_265408
  have hstable : (prefixWord ++ tailWord_265408).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265408).length < 2 ^ (prefixWord ++ tailWord_265408).sum := by decide
  have hdescent : baseEnd_265408 < baseStart_265408 := by decide
  rcases family_descends (prefixWord ++ tailWord_265408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265429 : List Nat := [1, 3, 2, 4, 1, 1, 1, 6]
def baseStart_265429 : Nat := 118140960795 + 265429 * 2 ^ 59
def prefixEnd_265429 : Nat := 4983230072969 + 3 ^ 40 * 265429 * 2
def baseEnd_265429 : Nat := 80766018751020587565523

theorem tailTrace_265429 : CollatzResearch.WordTrace tailWord_265429 prefixEnd_265429 80766018751020587565523 := by
  unfold tailWord_265429
  simp only [CollatzResearch.WordTrace]
  refine ⟨9680990955403539509271341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6453993970269026339514227 9680990955403539509271341)
  ·
    refine ⟨3630371608276327315976753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9680990955403539509271341 3630371608276327315976753)
    ·
      refine ⟨2722778706207245486982565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3630371608276327315976753 2722778706207245486982565)
      ·
        refine ⟨510521007413858528809231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2722778706207245486982565 510521007413858528809231)
        ·
          refine ⟨765781511120787793213847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510521007413858528809231 765781511120787793213847)
          ·
            refine ⟨1148672266681181689820771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765781511120787793213847 1148672266681181689820771)
            ·
              refine ⟨1723008400021772534731157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148672266681181689820771 1723008400021772534731157)
              ·
                refine ⟨80766018751020587565523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1723008400021772534731157 80766018751020587565523)
                ·
                  rfl

theorem cell19_265429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_265429 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265429 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265429 prefixEnd_265429 := by exact prefixLift 265429
  have htrace : WordTrace (prefixWord ++ tailWord_265429) baseStart_265429 baseEnd_265429 := by
    simpa [prefixWord, tailWord_265429, baseEnd_265429] using wordTrace_append hprefix tailTrace_265429
  have hstable : (prefixWord ++ tailWord_265429).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265429).length < 2 ^ (prefixWord ++ tailWord_265429).sum := by decide
  have hdescent : baseEnd_265429 < baseStart_265429 := by decide
  rcases family_descends (prefixWord ++ tailWord_265429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265431 : List Nat := [1, 1, 3, 2, 1, 2, 3, 6]
def baseStart_265431 : Nat := 118140960795 + 265431 * 2 ^ 59
def prefixEnd_265431 : Nat := 4983230072969 + 3 ^ 40 * 265431 * 2
def baseEnd_265431 : Nat := 80766627320685175521073

theorem tailTrace_265431 : CollatzResearch.WordTrace tailWord_265431 prefixEnd_265431 80766627320685175521073 := by
  unfold tailWord_265431
  simp only [CollatzResearch.WordTrace]
  refine ⟨9681063901396293850844147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6454042600930862567229431 9681063901396293850844147)
  ·
    refine ⟨14521595852094440776266221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9681063901396293850844147 14521595852094440776266221)
    ·
      refine ⟨5445598444535415291099833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14521595852094440776266221 5445598444535415291099833)
      ·
        refine ⟨4084198833401561468324875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5445598444535415291099833 4084198833401561468324875)
        ·
          refine ⟨6126298250102342202487313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4084198833401561468324875 6126298250102342202487313)
          ·
            refine ⟨4594723687576756651865485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6126298250102342202487313 4594723687576756651865485)
            ·
              refine ⟨1723021382841283744449557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4594723687576756651865485 1723021382841283744449557)
              ·
                refine ⟨80766627320685175521073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1723021382841283744449557 80766627320685175521073)
                ·
                  rfl

theorem cell19_265431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_265431 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265431 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265431 prefixEnd_265431 := by exact prefixLift 265431
  have htrace : WordTrace (prefixWord ++ tailWord_265431) baseStart_265431 baseEnd_265431 := by
    simpa [prefixWord, tailWord_265431, baseEnd_265431] using wordTrace_append hprefix tailTrace_265431
  have hstable : (prefixWord ++ tailWord_265431).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265431).length < 2 ^ (prefixWord ++ tailWord_265431).sum := by decide
  have hdescent : baseEnd_265431 < baseStart_265431 := by decide
  rcases family_descends (prefixWord ++ tailWord_265431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265486 : List Nat := [4, 1, 1, 2, 1, 3, 3, 4]
def baseStart_265486 : Nat := 118140960795 + 265486 * 2 ^ 59
def prefixEnd_265486 : Nat := 4983230072969 + 3 ^ 40 * 265486 * 2
def baseEnd_265486 : Nat := 80783362986461344298701

theorem tailTrace_265486 : CollatzResearch.WordTrace tailWord_265486 prefixEnd_265486 80783362986461344298701 := by
  unfold tailWord_265486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1210383739524629780512039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6455379944131358829397541 1210383739524629780512039)
  ·
    refine ⟨1815575609286944670768059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1210383739524629780512039 1815575609286944670768059)
    ·
      refine ⟨2723363413930417006152089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1815575609286944670768059 2723363413930417006152089)
      ·
        refine ⟨2042522560447812754614067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2723363413930417006152089 2042522560447812754614067)
        ·
          refine ⟨3063783840671719131921101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2042522560447812754614067 3063783840671719131921101)
          ·
            refine ⟨1148918940251894674470413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3063783840671719131921101 1148918940251894674470413)
            ·
              refine ⟨430844602594460502926405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1148918940251894674470413 430844602594460502926405)
              ·
                refine ⟨80783362986461344298701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 430844602594460502926405 80783362986461344298701)
                ·
                  rfl

theorem cell19_265486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_265486 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265486 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265486 prefixEnd_265486 := by exact prefixLift 265486
  have htrace : WordTrace (prefixWord ++ tailWord_265486) baseStart_265486 baseEnd_265486 := by
    simpa [prefixWord, tailWord_265486, baseEnd_265486] using wordTrace_append hprefix tailTrace_265486
  have hstable : (prefixWord ++ tailWord_265486).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265486).length < 2 ^ (prefixWord ++ tailWord_265486).sum := by decide
  have hdescent : baseEnd_265486 < baseStart_265486 := by decide
  rcases family_descends (prefixWord ++ tailWord_265486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265503 : List Nat := [1, 1, 2, 4, 4, 1, 3, 3]
def baseStart_265503 : Nat := 118140960795 + 265503 * 2 ^ 59
def prefixEnd_265503 : Nat := 4983230072969 + 3 ^ 40 * 265503 * 2
def baseEnd_265503 : Nat := 80788535828610341920877

theorem tailTrace_265503 : CollatzResearch.WordTrace tailWord_265503 prefixEnd_265503 80788535828610341920877 := by
  unfold tailWord_265503
  simp only [CollatzResearch.WordTrace]
  refine ⟨9683689957135450147465163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6455793304756966764976775 9683689957135450147465163)
  ·
    refine ⟨14525534935703175221197745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9683689957135450147465163 14525534935703175221197745)
    ·
      refine ⟨10894151201777381415898309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14525534935703175221197745 10894151201777381415898309)
      ·
        refine ⟨2042653350333259015480933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10894151201777381415898309 2042653350333259015480933)
        ·
          refine ⟨382997503187486065402675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2042653350333259015480933 382997503187486065402675)
          ·
            refine ⟨574496254781229098104013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382997503187486065402675 574496254781229098104013)
            ·
              refine ⟨215436095542960911789005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 574496254781229098104013 215436095542960911789005)
              ·
                refine ⟨80788535828610341920877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215436095542960911789005 80788535828610341920877)
                ·
                  rfl

theorem cell19_265503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 3].length) (baseStart_265503 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265503 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265503 prefixEnd_265503 := by exact prefixLift 265503
  have htrace : WordTrace (prefixWord ++ tailWord_265503) baseStart_265503 baseEnd_265503 := by
    simpa [prefixWord, tailWord_265503, baseEnd_265503] using wordTrace_append hprefix tailTrace_265503
  have hstable : (prefixWord ++ tailWord_265503).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265503).length < 2 ^ (prefixWord ++ tailWord_265503).sum := by decide
  have hdescent : baseEnd_265503 < baseStart_265503 := by decide
  rcases family_descends (prefixWord ++ tailWord_265503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265524 : List Nat := [2, 5, 1, 1, 1, 1, 8]
def baseStart_265524 : Nat := 118140960795 + 265524 * 2 ^ 59
def prefixEnd_265524 : Nat := 4983230072969 + 3 ^ 40 * 265524 * 2
def baseEnd_265524 : Nat := 26931641936696171818051

theorem tailTrace_265524 : CollatzResearch.WordTrace tailWord_265524 prefixEnd_265524 26931641936696171818051 := by
  unfold tailWord_265524
  simp only [CollatzResearch.WordTrace]
  refine ⟨4842227945029685366989813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6456303926706247155986417 4842227945029685366989813)
  ·
    refine ⟨453958869846533003155295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4842227945029685366989813 453958869846533003155295)
    ·
      refine ⟨680938304769799504732943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453958869846533003155295 680938304769799504732943)
      ·
        refine ⟨1021407457154699257099415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680938304769799504732943 1021407457154699257099415)
        ·
          refine ⟨1532111185732048885649123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021407457154699257099415 1532111185732048885649123)
          ·
            refine ⟨2298166778598073328473685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1532111185732048885649123 2298166778598073328473685)
            ·
              refine ⟨26931641936696171818051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2298166778598073328473685 26931641936696171818051)
              ·
                rfl

theorem cell19_265524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 8].length) (baseStart_265524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265524 prefixEnd_265524 := by exact prefixLift 265524
  have htrace : WordTrace (prefixWord ++ tailWord_265524) baseStart_265524 baseEnd_265524 := by
    simpa [prefixWord, tailWord_265524, baseEnd_265524] using wordTrace_append hprefix tailTrace_265524
  have hstable : (prefixWord ++ tailWord_265524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265524).length < 2 ^ (prefixWord ++ tailWord_265524).sum := by decide
  have hdescent : baseEnd_265524 < baseStart_265524 := by decide
  rcases family_descends (prefixWord ++ tailWord_265524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265562 : List Nat := [3, 1, 1, 2, 1, 2, 6, 3]
def baseStart_265562 : Nat := 118140960795 + 265562 * 2 ^ 59
def prefixEnd_265562 : Nat := 4983230072969 + 3 ^ 40 * 265562 * 2
def baseEnd_265562 : Nat := 80806488633715686609605

theorem tailTrace_265562 : CollatzResearch.WordTrace tailWord_265562 prefixEnd_265562 80806488633715686609605 := by
  unfold tailWord_265562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2421460465980425805965735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6457227909281135482575293 2421460465980425805965735)
  ·
    refine ⟨3632190698970638708948603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2421460465980425805965735 3632190698970638708948603)
    ·
      refine ⟨5448286048455958063422905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3632190698970638708948603 5448286048455958063422905)
      ·
        refine ⟨4086214536341968547567179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5448286048455958063422905 4086214536341968547567179)
        ·
          refine ⟨6129321804512952821350769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4086214536341968547567179 6129321804512952821350769)
          ·
            refine ⟨4596991353384714616013077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6129321804512952821350769 4596991353384714616013077)
            ·
              refine ⟨215483969689908497625613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4596991353384714616013077 215483969689908497625613)
              ·
                refine ⟨80806488633715686609605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215483969689908497625613 80806488633715686609605)
                ·
                  rfl

theorem cell19_265562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_265562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265562 prefixEnd_265562 := by exact prefixLift 265562
  have htrace : WordTrace (prefixWord ++ tailWord_265562) baseStart_265562 baseEnd_265562 := by
    simpa [prefixWord, tailWord_265562, baseEnd_265562] using wordTrace_append hprefix tailTrace_265562
  have hstable : (prefixWord ++ tailWord_265562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265562).length < 2 ^ (prefixWord ++ tailWord_265562).sum := by decide
  have hdescent : baseEnd_265562 < baseStart_265562 := by decide
  rcases family_descends (prefixWord ++ tailWord_265562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265581 : List Nat := [1, 5, 1, 1, 1, 5, 5]
def baseStart_265581 : Nat := 118140960795 + 265581 * 2 ^ 59
def prefixEnd_265581 : Nat := 4983230072969 + 3 ^ 40 * 265581 * 2
def baseEnd_265581 : Nat := 26937423348509757395777

theorem tailTrace_265581 : CollatzResearch.WordTrace tailWord_265581 prefixEnd_265581 26937423348509757395777 := by
  unfold tailWord_265581
  simp only [CollatzResearch.WordTrace]
  refine ⟨9686534850852869468804597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6457689900568579645869731 9686534850852869468804597)
  ·
    refine ⟨908112642267456512700431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9686534850852869468804597 908112642267456512700431)
    ·
      refine ⟨1362168963401184769050647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 908112642267456512700431 1362168963401184769050647)
      ·
        refine ⟨2043253445101777153575971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1362168963401184769050647 2043253445101777153575971)
        ·
          refine ⟨3064880167652665730363957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2043253445101777153575971 3064880167652665730363957)
          ·
            refine ⟨287332515717437412221621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3064880167652665730363957 287332515717437412221621)
            ·
              refine ⟨26937423348509757395777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287332515717437412221621 26937423348509757395777)
              ·
                rfl

theorem cell19_265581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 5].length) (baseStart_265581 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265581 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265581 prefixEnd_265581 := by exact prefixLift 265581
  have htrace : WordTrace (prefixWord ++ tailWord_265581) baseStart_265581 baseEnd_265581 := by
    simpa [prefixWord, tailWord_265581, baseEnd_265581] using wordTrace_append hprefix tailTrace_265581
  have hstable : (prefixWord ++ tailWord_265581).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265581).length < 2 ^ (prefixWord ++ tailWord_265581).sum := by decide
  have hdescent : baseEnd_265581 < baseStart_265581 := by decide
  rcases family_descends (prefixWord ++ tailWord_265581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265621 : List Nat := [1, 3, 2, 1, 1, 2, 4, 5]
def baseStart_265621 : Nat := 118140960795 + 265621 * 2 ^ 59
def prefixEnd_265621 : Nat := 4983230072969 + 3 ^ 40 * 265621 * 2
def baseEnd_265621 : Nat := 80824441438821031298333

theorem tailTrace_265621 : CollatzResearch.WordTrace tailWord_265621 prefixEnd_265621 80824441438821031298333 := by
  unfold tailWord_265621
  simp only [CollatzResearch.WordTrace]
  refine ⟨9687993770707956300260717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6458662513805304200173811 9687993770707956300260717)
  ·
    refine ⟨3632997664015483612597769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9687993770707956300260717 3632997664015483612597769)
    ·
      refine ⟨2724748248011612709448327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3632997664015483612597769 2724748248011612709448327)
      ·
        refine ⟨4087122372017419064172491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2724748248011612709448327 4087122372017419064172491)
        ·
          refine ⟨6130683558026128596258737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4087122372017419064172491 6130683558026128596258737)
          ·
            refine ⟨4598012668519596447194053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6130683558026128596258737 4598012668519596447194053)
            ·
              refine ⟨862127375347424333848885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4598012668519596447194053 862127375347424333848885)
              ·
                refine ⟨80824441438821031298333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 862127375347424333848885 80824441438821031298333)
                ·
                  rfl

theorem cell19_265621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_265621 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265621 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265621 prefixEnd_265621 := by exact prefixLift 265621
  have htrace : WordTrace (prefixWord ++ tailWord_265621) baseStart_265621 baseEnd_265621 := by
    simpa [prefixWord, tailWord_265621, baseEnd_265621] using wordTrace_append hprefix tailTrace_265621
  have hstable : (prefixWord ++ tailWord_265621).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265621).length < 2 ^ (prefixWord ++ tailWord_265621).sum := by decide
  have hdescent : baseEnd_265621 < baseStart_265621 := by decide
  rcases family_descends (prefixWord ++ tailWord_265621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265678 : List Nat := [4, 1, 1, 1, 2, 1, 2, 7]
def baseStart_265678 : Nat := 118140960795 + 265678 * 2 ^ 59
def prefixEnd_265678 : Nat := 4983230072969 + 3 ^ 40 * 265678 * 2
def baseEnd_265678 : Nat := 80841785674261788031511

theorem tailTrace_265678 : CollatzResearch.WordTrace tailWord_265678 prefixEnd_265678 80841785674261788031511 := by
  unfold tailWord_265678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1211259091437681879385711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6460048487667636690057125 1211259091437681879385711)
  ·
    refine ⟨1816888637156522819078567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1211259091437681879385711 1816888637156522819078567)
    ·
      refine ⟨2725332955734784228617851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1816888637156522819078567 2725332955734784228617851)
      ·
        refine ⟨4087999433602176342926777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2725332955734784228617851 4087999433602176342926777)
        ·
          refine ⟨3065999575201632257195083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4087999433602176342926777 3065999575201632257195083)
          ·
            refine ⟨4598999362802448385792625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3065999575201632257195083 4598999362802448385792625)
            ·
              refine ⟨3449249522101836289344469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4598999362802448385792625 3449249522101836289344469)
              ·
                refine ⟨80841785674261788031511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3449249522101836289344469 80841785674261788031511)
                ·
                  rfl

theorem cell19_265678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_265678 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265678 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265678 prefixEnd_265678 := by exact prefixLift 265678
  have htrace : WordTrace (prefixWord ++ tailWord_265678) baseStart_265678 baseEnd_265678 := by
    simpa [prefixWord, tailWord_265678, baseEnd_265678] using wordTrace_append hprefix tailTrace_265678
  have hstable : (prefixWord ++ tailWord_265678).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265678).length < 2 ^ (prefixWord ++ tailWord_265678).sum := by decide
  have hdescent : baseEnd_265678 < baseStart_265678 := by decide
  rcases family_descends (prefixWord ++ tailWord_265678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265697 : List Nat := [1, 2, 3, 1, 2, 4, 6]
def baseStart_265697 : Nat := 118140960795 + 265697 * 2 ^ 59
def prefixEnd_265697 : Nat := 4983230072969 + 3 ^ 40 * 265697 * 2
def baseEnd_265697 : Nat := 26949189028691791203079

theorem tailTrace_265697 : CollatzResearch.WordTrace tailWord_265697 prefixEnd_265697 26949189028691791203079 := by
  unfold tailWord_265697
  simp only [CollatzResearch.WordTrace]
  refine ⟨9690765718432621280027345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6460510478955080853351563 9690765718432621280027345)
  ·
    refine ⟨7268074288824465960020509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9690765718432621280027345 7268074288824465960020509)
    ·
      refine ⟨2725527858309174735007691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7268074288824465960020509 2725527858309174735007691)
      ·
        refine ⟨4088291787463762102511537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2725527858309174735007691 4088291787463762102511537)
        ·
          refine ⟨3066218840597821576883653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4088291787463762102511537 3066218840597821576883653)
          ·
            refine ⟨574916032612091545665685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3066218840597821576883653 574916032612091545665685)
            ·
              refine ⟨26949189028691791203079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 574916032612091545665685 26949189028691791203079)
              ·
                rfl

theorem cell19_265697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 6].length) (baseStart_265697 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265697 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265697 prefixEnd_265697 := by exact prefixLift 265697
  have htrace : WordTrace (prefixWord ++ tailWord_265697) baseStart_265697 baseEnd_265697 := by
    simpa [prefixWord, tailWord_265697, baseEnd_265697] using wordTrace_append hprefix tailTrace_265697
  have hstable : (prefixWord ++ tailWord_265697).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265697).length < 2 ^ (prefixWord ++ tailWord_265697).sum := by decide
  have hdescent : baseEnd_265697 < baseStart_265697 := by decide
  rcases family_descends (prefixWord ++ tailWord_265697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265729 : List Nat := [1, 2, 4, 1, 5, 1, 2, 3]
def baseStart_265729 : Nat := 118140960795 + 265729 * 2 ^ 59
def prefixEnd_265729 : Nat := 4983230072969 + 3 ^ 40 * 265729 * 2
def baseEnd_265729 : Nat := 80857304200708780898039

theorem tailTrace_265729 : CollatzResearch.WordTrace tailWord_265729 prefixEnd_265729 80857304200708780898039 := by
  unfold tailWord_265729
  simp only [CollatzResearch.WordTrace]
  refine ⟨9691932854316690745192241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6461288569544460496794827 9691932854316690745192241)
  ·
    refine ⟨7268949640737518058894181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9691932854316690745192241 7268949640737518058894181)
    ·
      refine ⟨1362928057638284636042659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7268949640737518058894181 1362928057638284636042659)
      ·
        refine ⟨2044392086457426954063989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1362928057638284636042659 2044392086457426954063989)
        ·
          refine ⟨191661758105383776943499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2044392086457426954063989 191661758105383776943499)
          ·
            refine ⟨287492637158075665415249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191661758105383776943499 287492637158075665415249)
            ·
              refine ⟨215619477868556749061437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287492637158075665415249 215619477868556749061437)
              ·
                refine ⟨80857304200708780898039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215619477868556749061437 80857304200708780898039)
                ·
                  rfl

theorem cell19_265729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 3].length) (baseStart_265729 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265729 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265729 prefixEnd_265729 := by exact prefixLift 265729
  have htrace : WordTrace (prefixWord ++ tailWord_265729) baseStart_265729 baseEnd_265729 := by
    simpa [prefixWord, tailWord_265729, baseEnd_265729] using wordTrace_append hprefix tailTrace_265729
  have hstable : (prefixWord ++ tailWord_265729).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265729).length < 2 ^ (prefixWord ++ tailWord_265729).sum := by decide
  have hdescent : baseEnd_265729 < baseStart_265729 := by decide
  rcases family_descends (prefixWord ++ tailWord_265729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265748 : List Nat := [2, 4, 3, 1, 3, 1, 5]
def baseStart_265748 : Nat := 118140960795 + 265748 * 2 ^ 59
def prefixEnd_265748 : Nat := 4983230072969 + 3 ^ 40 * 265748 * 2
def baseEnd_265748 : Nat := 26954361870840788825255

theorem tailTrace_265748 : CollatzResearch.WordTrace tailWord_265748 prefixEnd_265748 26954361870840788825255 := by
  unfold tailWord_265748
  simp only [CollatzResearch.WordTrace]
  refine ⟨4846312920623928495066949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6461750560831904660089265 4846312920623928495066949)
  ·
    refine ⟨908683672616986592825053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4846312920623928495066949 908683672616986592825053)
    ·
      refine ⟨340756377231369972309395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 908683672616986592825053 340756377231369972309395)
      ·
        refine ⟨511134565847054958464093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340756377231369972309395 511134565847054958464093)
        ·
          refine ⟨191675462192645609424035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511134565847054958464093 191675462192645609424035)
          ·
            refine ⟨287513193288968414136053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191675462192645609424035 287513193288968414136053)
            ·
              refine ⟨26954361870840788825255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287513193288968414136053 26954361870840788825255)
              ·
                rfl

theorem cell19_265748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 5].length) (baseStart_265748 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265748 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265748 prefixEnd_265748 := by exact prefixLift 265748
  have htrace : WordTrace (prefixWord ++ tailWord_265748) baseStart_265748 baseEnd_265748 := by
    simpa [prefixWord, tailWord_265748, baseEnd_265748] using wordTrace_append hprefix tailTrace_265748
  have hstable : (prefixWord ++ tailWord_265748).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265748).length < 2 ^ (prefixWord ++ tailWord_265748).sum := by decide
  have hdescent : baseEnd_265748 < baseStart_265748 := by decide
  rcases family_descends (prefixWord ++ tailWord_265748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265752 : List Nat := [2, 1, 2, 3, 4, 2, 5]
def baseStart_265752 : Nat := 118140960795 + 265752 * 2 ^ 59
def prefixEnd_265752 : Nat := 4983230072969 + 3 ^ 40 * 265752 * 2
def baseEnd_265752 : Nat := 26954767583950514128955

theorem tailTrace_265752 : CollatzResearch.WordTrace tailWord_265752 prefixEnd_265752 26954767583950514128955 := by
  unfold tailWord_265752
  simp only [CollatzResearch.WordTrace]
  refine ⟨4846385866616682836639755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6461847822155577115519673 4846385866616682836639755)
  ·
    refine ⟨7269578799925024254959633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4846385866616682836639755 7269578799925024254959633)
    ·
      refine ⟨5452184099943768191219725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7269578799925024254959633 5452184099943768191219725)
      ·
        refine ⟨2044569037478913071707397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5452184099943768191219725 2044569037478913071707397)
        ·
          refine ⟨383356694527296200945137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2044569037478913071707397 383356694527296200945137)
          ·
            refine ⟨287517520895472150708853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383356694527296200945137 287517520895472150708853)
            ·
              refine ⟨26954767583950514128955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287517520895472150708853 26954767583950514128955)
              ·
                rfl

theorem cell19_265752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 5].length) (baseStart_265752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265752 prefixEnd_265752 := by exact prefixLift 265752
  have htrace : WordTrace (prefixWord ++ tailWord_265752) baseStart_265752 baseEnd_265752 := by
    simpa [prefixWord, tailWord_265752, baseEnd_265752] using wordTrace_append hprefix tailTrace_265752
  have hstable : (prefixWord ++ tailWord_265752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265752).length < 2 ^ (prefixWord ++ tailWord_265752).sum := by decide
  have hdescent : baseEnd_265752 < baseStart_265752 := by decide
  rcases family_descends (prefixWord ++ tailWord_265752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265828 : List Nat := [2, 3, 1, 1, 2, 5, 1, 4]
def baseStart_265828 : Nat := 118140960795 + 265828 * 2 ^ 59
def prefixEnd_265828 : Nat := 4983230072969 + 3 ^ 40 * 265828 * 2
def baseEnd_265828 : Nat := 80887428399105884697769

theorem tailTrace_265828 : CollatzResearch.WordTrace tailWord_265828 prefixEnd_265828 80887428399105884697769 := by
  unfold tailWord_265828
  simp only [CollatzResearch.WordTrace]
  refine ⟨4847771840479015326523069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6463695787305353768697425 4847771840479015326523069)
  ·
    refine ⟨1817914440179630747446151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4847771840479015326523069 1817914440179630747446151)
    ·
      refine ⟨2726871660269446121169227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1817914440179630747446151 2726871660269446121169227)
      ·
        refine ⟨4090307490404169181753841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2726871660269446121169227 4090307490404169181753841)
        ·
          refine ⟨3067730617803126886315381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4090307490404169181753841 3067730617803126886315381)
          ·
            refine ⟨287599745419043145592067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3067730617803126886315381 287599745419043145592067)
            ·
              refine ⟨431399618128564718388101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287599745419043145592067 431399618128564718388101)
              ·
                refine ⟨80887428399105884697769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 431399618128564718388101 80887428399105884697769)
                ·
                  rfl

theorem cell19_265828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_265828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265828 prefixEnd_265828 := by exact prefixLift 265828
  have htrace : WordTrace (prefixWord ++ tailWord_265828) baseStart_265828 baseEnd_265828 := by
    simpa [prefixWord, tailWord_265828, baseEnd_265828] using wordTrace_append hprefix tailTrace_265828
  have hstable : (prefixWord ++ tailWord_265828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265828).length < 2 ^ (prefixWord ++ tailWord_265828).sum := by decide
  have hdescent : baseEnd_265828 < baseStart_265828 := by decide
  rcases family_descends (prefixWord ++ tailWord_265828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265845 : List Nat := [1, 3, 4, 2, 1, 2, 3, 3]
def baseStart_265845 : Nat := 118140960795 + 265845 * 2 ^ 59
def prefixEnd_265845 : Nat := 4983230072969 + 3 ^ 40 * 265845 * 2
def baseEnd_265845 : Nat := 80892601241254882319945

theorem tailTrace_265845 : CollatzResearch.WordTrace tailWord_265845 prefixEnd_265845 80892601241254882319945 := by
  unfold tailWord_265845
  simp only [CollatzResearch.WordTrace]
  refine ⟨9696163721896442556414989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6464109147930961704276659 9696163721896442556414989)
  ·
    refine ⟨3636061395711165958655621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9696163721896442556414989 3636061395711165958655621)
    ·
      refine ⟨681761511695843617247929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3636061395711165958655621 681761511695843617247929)
      ·
        refine ⟨511321133771882712935947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681761511695843617247929 511321133771882712935947)
        ·
          refine ⟨766981700657824069403921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511321133771882712935947 766981700657824069403921)
          ·
            refine ⟨575236275493368052052941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766981700657824069403921 575236275493368052052941)
            ·
              refine ⟨215713603310013019519853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 575236275493368052052941 215713603310013019519853)
              ·
                refine ⟨80892601241254882319945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215713603310013019519853 80892601241254882319945)
                ·
                  rfl

theorem cell19_265845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 3].length) (baseStart_265845 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265845 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265845 prefixEnd_265845 := by exact prefixLift 265845
  have htrace : WordTrace (prefixWord ++ tailWord_265845) baseStart_265845 baseEnd_265845 := by
    simpa [prefixWord, tailWord_265845, baseEnd_265845] using wordTrace_append hprefix tailTrace_265845
  have hstable : (prefixWord ++ tailWord_265845).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265845).length < 2 ^ (prefixWord ++ tailWord_265845).sum := by decide
  have hdescent : baseEnd_265845 < baseStart_265845 := by decide
  rcases family_descends (prefixWord ++ tailWord_265845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265896 : List Nat := [2, 1, 7, 1, 2, 1, 2, 3]
def baseStart_265896 : Nat := 118140960795 + 265896 * 2 ^ 59
def prefixEnd_265896 : Nat := 4983230072969 + 3 ^ 40 * 265896 * 2
def baseEnd_265896 : Nat := 80908119767701875186473

theorem tailTrace_265896 : CollatzResearch.WordTrace tailWord_265896 prefixEnd_265896 80908119767701875186473 := by
  unfold tailWord_265896
  simp only [CollatzResearch.WordTrace]
  refine ⟨4849011922355839133260771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6465349229807785511014361 4849011922355839133260771)
  ·
    refine ⟨7273517883533758699891157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4849011922355839133260771 7273517883533758699891157)
    ·
      refine ⟨170473075395322469528699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 7273517883533758699891157 170473075395322469528699)
      ·
        refine ⟨255709613092983704293049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170473075395322469528699 255709613092983704293049)
        ·
          refine ⟨191782209819737778219787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255709613092983704293049 191782209819737778219787)
          ·
            refine ⟨287673314729606667329681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191782209819737778219787 287673314729606667329681)
            ·
              refine ⟨215754986047205000497261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287673314729606667329681 215754986047205000497261)
              ·
                refine ⟨80908119767701875186473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215754986047205000497261 80908119767701875186473)
                ·
                  rfl

theorem cell19_265896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 3].length) (baseStart_265896 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265896 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265896 prefixEnd_265896 := by exact prefixLift 265896
  have htrace : WordTrace (prefixWord ++ tailWord_265896) baseStart_265896 baseEnd_265896 := by
    simpa [prefixWord, tailWord_265896, baseEnd_265896] using wordTrace_append hprefix tailTrace_265896
  have hstable : (prefixWord ++ tailWord_265896).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265896).length < 2 ^ (prefixWord ++ tailWord_265896).sum := by decide
  have hdescent : baseEnd_265896 < baseStart_265896 := by decide
  rcases family_descends (prefixWord ++ tailWord_265896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265902 : List Nat := [4, 1, 4, 1, 2, 1, 1, 5]
def baseStart_265902 : Nat := 118140960795 + 265902 * 2 ^ 59
def prefixEnd_265902 : Nat := 4983230072969 + 3 ^ 40 * 265902 * 2
def baseEnd_265902 : Nat := 80909945476695639053123

theorem tailTrace_265902 : CollatzResearch.WordTrace tailWord_265902 prefixEnd_265902 80909945476695639053123 := by
  unfold tailWord_265902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1212280335336242661404995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6465495121793294194159973 1212280335336242661404995)
  ·
    refine ⟨1818420503004363992107493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1212280335336242661404995 1818420503004363992107493)
    ·
      refine ⟨340953844313318248520155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1818420503004363992107493 340953844313318248520155)
      ·
        refine ⟨511430766469977372780233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340953844313318248520155 511430766469977372780233)
        ·
          refine ⟨383573074852483029585175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511430766469977372780233 383573074852483029585175)
          ·
            refine ⟨575359612278724544377763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383573074852483029585175 575359612278724544377763)
            ·
              refine ⟨863039418418086816566645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575359612278724544377763 863039418418086816566645)
              ·
                refine ⟨80909945476695639053123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 863039418418086816566645 80909945476695639053123)
                ·
                  rfl

theorem cell19_265902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_265902 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265902 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265902 prefixEnd_265902 := by exact prefixLift 265902
  have htrace : WordTrace (prefixWord ++ tailWord_265902) baseStart_265902 baseEnd_265902 := by
    simpa [prefixWord, tailWord_265902, baseEnd_265902] using wordTrace_append hprefix tailTrace_265902
  have hstable : (prefixWord ++ tailWord_265902).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265902).length < 2 ^ (prefixWord ++ tailWord_265902).sum := by decide
  have hdescent : baseEnd_265902 < baseStart_265902 := by decide
  rcases family_descends (prefixWord ++ tailWord_265902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265944 : List Nat := [2, 1, 2, 2, 3, 1, 4, 4]
def baseStart_265944 : Nat := 118140960795 + 265944 * 2 ^ 59
def prefixEnd_265944 : Nat := 4983230072969 + 3 ^ 40 * 265944 * 2
def baseEnd_265944 : Nat := 80922725439651986119675

theorem tailTrace_265944 : CollatzResearch.WordTrace tailWord_265944 prefixEnd_265944 80922725439651986119675 := by
  unfold tailWord_265944
  simp only [CollatzResearch.WordTrace]
  refine ⟨4849887274268891232134443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6466516365691854976179257 4849887274268891232134443)
  ·
    refine ⟨7274830911403336848201665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4849887274268891232134443 7274830911403336848201665)
    ·
      refine ⟨5456123183552502636151249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7274830911403336848201665 5456123183552502636151249)
      ·
        refine ⟨4092092387664376977113437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5456123183552502636151249 4092092387664376977113437)
        ·
          refine ⟨1534534645374141366417539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4092092387664376977113437 1534534645374141366417539)
          ·
            refine ⟨2301801968061212049626309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534534645374141366417539 2301801968061212049626309)
            ·
              refine ⟨431587869011477259304933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2301801968061212049626309 431587869011477259304933)
              ·
                refine ⟨80922725439651986119675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 431587869011477259304933 80922725439651986119675)
                ·
                  rfl

theorem cell19_265944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_265944 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265944 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265944 prefixEnd_265944 := by exact prefixLift 265944
  have htrace : WordTrace (prefixWord ++ tailWord_265944) baseStart_265944 baseEnd_265944 := by
    simpa [prefixWord, tailWord_265944, baseEnd_265944] using wordTrace_append hprefix tailTrace_265944
  have hstable : (prefixWord ++ tailWord_265944).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265944).length < 2 ^ (prefixWord ++ tailWord_265944).sum := by decide
  have hdescent : baseEnd_265944 < baseStart_265944 := by decide
  rcases family_descends (prefixWord ++ tailWord_265944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265982 : List Nat := [4, 2, 2, 1, 10]
def baseStart_265982 : Nat := 118140960795 + 265982 * 2 ^ 59
def prefixEnd_265982 : Nat := 4983230072969 + 3 ^ 40 * 265982 * 2
def baseEnd_265982 : Nat := 2997566231973302121301

theorem tailTrace_265982 : CollatzResearch.WordTrace tailWord_265982 prefixEnd_265982 2997566231973302121301 := by
  unfold tailWord_265982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1212645065300014369269025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6467440348266743302768133 1212645065300014369269025)
  ·
    refine ⟨909483798975010776951769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1212645065300014369269025 909483798975010776951769)
    ·
      refine ⟨682112849231258082713827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 909483798975010776951769 682112849231258082713827)
      ·
        refine ⟨1023169273846887124070741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682112849231258082713827 1023169273846887124070741)
        ·
          refine ⟨2997566231973302121301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1023169273846887124070741 2997566231973302121301)
          ·
            rfl

theorem cell19_265982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 10].length) (baseStart_265982 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_265982 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_265982 prefixEnd_265982 := by exact prefixLift 265982
  have htrace : WordTrace (prefixWord ++ tailWord_265982) baseStart_265982 baseEnd_265982 := by
    simpa [prefixWord, tailWord_265982, baseEnd_265982] using wordTrace_append hprefix tailTrace_265982
  have hstable : (prefixWord ++ tailWord_265982).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265982).length < 2 ^ (prefixWord ++ tailWord_265982).sum := by decide
  have hdescent : baseEnd_265982 < baseStart_265982 := by decide
  rcases family_descends (prefixWord ++ tailWord_265982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266003 : List Nat := [1, 1, 1, 2, 1, 3, 2, 8]
def baseStart_266003 : Nat := 118140960795 + 266003 * 2 ^ 59
def prefixEnd_266003 : Nat := 4983230072969 + 3 ^ 40 * 266003 * 2
def baseEnd_266003 : Nat := 80940678244757330808403

theorem tailTrace_266003 : CollatzResearch.WordTrace tailWord_266003 prefixEnd_266003 80940678244757330808403 := by
  unfold tailWord_266003
  simp only [CollatzResearch.WordTrace]
  refine ⟨9701926455324035540666663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6467950970216023693777775 9701926455324035540666663)
  ·
    refine ⟨14552889682986053310999995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9701926455324035540666663 14552889682986053310999995)
    ·
      refine ⟨21829334524479079966499993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14552889682986053310999995 21829334524479079966499993)
      ·
        refine ⟨16372000893359309974874995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21829334524479079966499993 16372000893359309974874995)
        ·
          refine ⟨24558001340038964962312493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16372000893359309974874995 24558001340038964962312493)
          ·
            refine ⟨9209250502514611860867185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24558001340038964962312493 9209250502514611860867185)
            ·
              refine ⟨6906937876885958895650389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9209250502514611860867185 6906937876885958895650389)
              ·
                refine ⟨80940678244757330808403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6906937876885958895650389 80940678244757330808403)
                ·
                  rfl

theorem cell19_266003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_266003 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_266003 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_266003 prefixEnd_266003 := by exact prefixLift 266003
  have htrace : WordTrace (prefixWord ++ tailWord_266003) baseStart_266003 baseEnd_266003 := by
    simpa [prefixWord, tailWord_266003, baseEnd_266003] using wordTrace_append hprefix tailTrace_266003
  have hstable : (prefixWord ++ tailWord_266003).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266003).length < 2 ^ (prefixWord ++ tailWord_266003).sum := by decide
  have hdescent : baseEnd_266003 < baseStart_266003 := by decide
  rcases family_descends (prefixWord ++ tailWord_266003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266018 : List Nat := [3, 3, 1, 1, 2, 1, 5, 3]
def baseStart_266018 : Nat := 118140960795 + 266018 * 2 ^ 59
def prefixEnd_266018 : Nat := 4983230072969 + 3 ^ 40 * 266018 * 2
def baseEnd_266018 : Nat := 80945242517241740475029

theorem tailTrace_266018 : CollatzResearch.WordTrace tailWord_266018 prefixEnd_266018 80945242517241740475029 := by
  unfold tailWord_266018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2425618387567423275615677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6468315700179795401641805 2425618387567423275615677)
  ·
    refine ⟨909606895337783728355879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2425618387567423275615677 909606895337783728355879)
    ·
      refine ⟨1364410343006675592533819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 909606895337783728355879 1364410343006675592533819)
      ·
        refine ⟨2046615514510013388800729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1364410343006675592533819 2046615514510013388800729)
        ·
          refine ⟨1534961635882510041600547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2046615514510013388800729 1534961635882510041600547)
          ·
            refine ⟨2302442453823765062400821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534961635882510041600547 2302442453823765062400821)
            ·
              refine ⟨215853980045977974600077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2302442453823765062400821 215853980045977974600077)
              ·
                refine ⟨80945242517241740475029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215853980045977974600077 80945242517241740475029)
                ·
                  rfl

theorem cell19_266018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_266018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_266018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_266018 prefixEnd_266018 := by exact prefixLift 266018
  have htrace : WordTrace (prefixWord ++ tailWord_266018) baseStart_266018 baseEnd_266018 := by
    simpa [prefixWord, tailWord_266018, baseEnd_266018] using wordTrace_append hprefix tailTrace_266018
  have hstable : (prefixWord ++ tailWord_266018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266018).length < 2 ^ (prefixWord ++ tailWord_266018).sum := by decide
  have hdescent : baseEnd_266018 < baseStart_266018 := by decide
  rcases family_descends (prefixWord ++ tailWord_266018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266094 : List Nat := [4, 1, 2, 3, 1, 3, 5]
def baseStart_266094 : Nat := 118140960795 + 266094 * 2 ^ 59
def prefixEnd_266094 : Nat := 4983230072969 + 3 ^ 40 * 266094 * 2
def baseEnd_266094 : Nat := 26989456054832027595311

theorem tailTrace_266094 : CollatzResearch.WordTrace tailWord_266094 prefixEnd_266094 26989456054832027595311 := by
  unfold tailWord_266094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1213155687249294760278667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6470163665329572054819557 1213155687249294760278667)
  ·
    refine ⟨1819733530873942140418001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1213155687249294760278667 1819733530873942140418001)
    ·
      refine ⟨1364800148155456605313501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1819733530873942140418001 1364800148155456605313501)
      ·
        refine ⟨511800055558296226992563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1364800148155456605313501 511800055558296226992563)
        ·
          refine ⟨767700083337444340488845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511800055558296226992563 767700083337444340488845)
          ·
            refine ⟨287887531251541627683317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 767700083337444340488845 287887531251541627683317)
            ·
              refine ⟨26989456054832027595311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287887531251541627683317 26989456054832027595311)
              ·
                rfl

theorem cell19_266094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 5].length) (baseStart_266094 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_266094 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_266094 prefixEnd_266094 := by exact prefixLift 266094
  have htrace : WordTrace (prefixWord ++ tailWord_266094) baseStart_266094 baseEnd_266094 := by
    simpa [prefixWord, tailWord_266094, baseEnd_266094] using wordTrace_append hprefix tailTrace_266094
  have hstable : (prefixWord ++ tailWord_266094).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266094).length < 2 ^ (prefixWord ++ tailWord_266094).sum := by decide
  have hdescent : baseEnd_266094 < baseStart_266094 := by decide
  rcases family_descends (prefixWord ++ tailWord_266094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266115 : List Nat := [1, 1, 1, 3, 4, 3, 2, 4]
def baseStart_266115 : Nat := 118140960795 + 266115 * 2 ^ 59
def prefixEnd_266115 : Nat := 4983230072969 + 3 ^ 40 * 266115 * 2
def baseEnd_266115 : Nat := 80974758145974256319209

theorem tailTrace_266115 : CollatzResearch.WordTrace tailWord_266115 prefixEnd_266115 80974758145974256319209 := by
  unfold tailWord_266115
  simp only [CollatzResearch.WordTrace]
  refine ⟨9706011430918278668743799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6470674287278852445829199 9706011430918278668743799)
  ·
    refine ⟨14559017146377418003115699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9706011430918278668743799 14559017146377418003115699)
    ·
      refine ⟨21838525719566127004673549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14559017146377418003115699 21838525719566127004673549)
      ·
        refine ⟨8189447144837297626752581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21838525719566127004673549 8189447144837297626752581)
        ·
          refine ⟨1535521339656993305016109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8189447144837297626752581 1535521339656993305016109)
          ·
            refine ⟨575820502371372489381041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1535521339656993305016109 575820502371372489381041)
            ·
              refine ⟨431865376778529367035781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575820502371372489381041 431865376778529367035781)
              ·
                refine ⟨80974758145974256319209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 431865376778529367035781 80974758145974256319209)
                ·
                  rfl

theorem cell19_266115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_266115 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_266115 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_266115 prefixEnd_266115 := by exact prefixLift 266115
  have htrace : WordTrace (prefixWord ++ tailWord_266115) baseStart_266115 baseEnd_266115 := by
    simpa [prefixWord, tailWord_266115, baseEnd_266115] using wordTrace_append hprefix tailTrace_266115
  have hstable : (prefixWord ++ tailWord_266115).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266115).length < 2 ^ (prefixWord ++ tailWord_266115).sum := by decide
  have hdescent : baseEnd_266115 < baseStart_266115 := by decide
  rcases family_descends (prefixWord ++ tailWord_266115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266191 : List Nat := [1, 1, 2, 1, 1, 5, 5, 3]
def baseStart_266191 : Nat := 118140960795 + 266191 * 2 ^ 59
def prefixEnd_266191 : Nat := 4983230072969 + 3 ^ 40 * 266191 * 2
def baseEnd_266191 : Nat := 80997883793228598630113

theorem tailTrace_266191 : CollatzResearch.WordTrace tailWord_266191 prefixEnd_266191 80997883793228598630113 := by
  unfold tailWord_266191
  simp only [CollatzResearch.WordTrace]
  refine ⟨9708783378642943648510427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6472522252428629099006951 9708783378642943648510427)
  ·
    refine ⟨14563175067964415472765641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9708783378642943648510427 14563175067964415472765641)
    ·
      refine ⟨10922381300973311604574231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14563175067964415472765641 10922381300973311604574231)
      ·
        refine ⟨16383571951459967406861347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10922381300973311604574231 16383571951459967406861347)
        ·
          refine ⟨24575357927189951110292021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16383571951459967406861347 24575357927189951110292021)
          ·
            refine ⟨2303939805674057916589877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24575357927189951110292021 2303939805674057916589877)
            ·
              refine ⟨215994356781942929680301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2303939805674057916589877 215994356781942929680301)
              ·
                refine ⟨80997883793228598630113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215994356781942929680301 80997883793228598630113)
                ·
                  rfl

theorem cell19_266191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 3].length) (baseStart_266191 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_266191 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_266191 prefixEnd_266191 := by exact prefixLift 266191
  have htrace : WordTrace (prefixWord ++ tailWord_266191) baseStart_266191 baseEnd_266191 := by
    simpa [prefixWord, tailWord_266191, baseEnd_266191] using wordTrace_append hprefix tailTrace_266191
  have hstable : (prefixWord ++ tailWord_266191).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266191).length < 2 ^ (prefixWord ++ tailWord_266191).sum := by decide
  have hdescent : baseEnd_266191 < baseStart_266191 := by decide
  rcases family_descends (prefixWord ++ tailWord_266191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266212 : List Nat := [2, 3, 1, 1, 1, 1, 10]
def baseStart_266212 : Nat := 118140960795 + 266212 * 2 ^ 59
def prefixEnd_266212 : Nat := 4983230072969 + 3 ^ 40 * 266212 * 2
def baseEnd_266212 : Nat := 27001424591568924054463

theorem tailTrace_266212 : CollatzResearch.WordTrace tailWord_266212 prefixEnd_266212 27001424591568924054463 := by
  unfold tailWord_266212
  simp only [CollatzResearch.WordTrace]
  refine ⟨4854774655783432117512445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6473032874377909490016593 4854774655783432117512445)
  ·
    refine ⟨1820540495918787044067167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4854774655783432117512445 1820540495918787044067167)
    ·
      refine ⟨2730810743878180566100751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1820540495918787044067167 2730810743878180566100751)
      ·
        refine ⟨4096216115817270849151127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2730810743878180566100751 4096216115817270849151127)
        ·
          refine ⟨6144324173725906273726691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4096216115817270849151127 6144324173725906273726691)
          ·
            refine ⟨9216486260588859410590037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6144324173725906273726691 9216486260588859410590037)
            ·
              refine ⟨27001424591568924054463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9216486260588859410590037 27001424591568924054463)
              ·
                rfl

theorem cell19_266212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 10].length) (baseStart_266212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_266212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_266212 prefixEnd_266212 := by exact prefixLift 266212
  have htrace : WordTrace (prefixWord ++ tailWord_266212) baseStart_266212 baseEnd_266212 := by
    simpa [prefixWord, tailWord_266212, baseEnd_266212] using wordTrace_append hprefix tailTrace_266212
  have hstable : (prefixWord ++ tailWord_266212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266212).length < 2 ^ (prefixWord ++ tailWord_266212).sum := by decide
  have hdescent : baseEnd_266212 < baseStart_266212 := by decide
  rcases family_descends (prefixWord ++ tailWord_266212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266286 : List Nat := [4, 1, 3, 1, 1, 2, 1, 6]
def baseStart_266286 : Nat := 118140960795 + 266286 * 2 ^ 59
def prefixEnd_266286 : Nat := 4983230072969 + 3 ^ 40 * 266286 * 2
def baseEnd_266286 : Nat := 81026790852296526518743

theorem tailTrace_266286 : CollatzResearch.WordTrace tailWord_266286 prefixEnd_266286 81026790852296526518743 := by
  unfold tailWord_266286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1214031039162346859152339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6474832208865849915479141 1214031039162346859152339)
  ·
    refine ⟨1821046558743520288728509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1214031039162346859152339 1821046558743520288728509)
    ·
      refine ⟨682892459528820108273191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1821046558743520288728509 682892459528820108273191)
      ·
        refine ⟨1024338689293230162409787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682892459528820108273191 1024338689293230162409787)
        ·
          refine ⟨1536508033939845243614681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1024338689293230162409787 1536508033939845243614681)
          ·
            refine ⟨1152381025454883932711011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1536508033939845243614681 1152381025454883932711011)
            ·
              refine ⟨1728571538182325899066517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152381025454883932711011 1728571538182325899066517)
              ·
                refine ⟨81026790852296526518743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1728571538182325899066517 81026790852296526518743)
                ·
                  rfl

theorem cell19_266286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_266286 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_266286 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_266286 prefixEnd_266286 := by exact prefixLift 266286
  have htrace : WordTrace (prefixWord ++ tailWord_266286) baseStart_266286 baseEnd_266286 := by
    simpa [prefixWord, tailWord_266286, baseEnd_266286] using wordTrace_append hprefix tailTrace_266286
  have hstable : (prefixWord ++ tailWord_266286).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266286).length < 2 ^ (prefixWord ++ tailWord_266286).sum := by decide
  have hdescent : baseEnd_266286 < baseStart_266286 := by decide
  rcases family_descends (prefixWord ++ tailWord_266286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266288 : List Nat := [2, 1, 1, 1, 2, 5, 1, 6]
def baseStart_266288 : Nat := 118140960795 + 266288 * 2 ^ 59
def prefixEnd_266288 : Nat := 4983230072969 + 3 ^ 40 * 266288 * 2
def baseEnd_266288 : Nat := 81027399421961114474293

theorem tailTrace_266288 : CollatzResearch.WordTrace tailWord_266288 prefixEnd_266288 81027399421961114474293 := by
  unfold tailWord_266288
  simp only [CollatzResearch.WordTrace]
  refine ⟨4856160629645764607395759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6474880839527686143194345 4856160629645764607395759)
  ·
    refine ⟨7284240944468646911093639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4856160629645764607395759 7284240944468646911093639)
    ·
      refine ⟨10926361416702970366640459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7284240944468646911093639 10926361416702970366640459)
      ·
        refine ⟨16389542125054455549960689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10926361416702970366640459 16389542125054455549960689)
        ·
          refine ⟨12292156593790841662470517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16389542125054455549960689 12292156593790841662470517)
          ·
            refine ⟨1152389680667891405856611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12292156593790841662470517 1152389680667891405856611)
            ·
              refine ⟨1728584521001837108784917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152389680667891405856611 1728584521001837108784917)
              ·
                refine ⟨81027399421961114474293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1728584521001837108784917 81027399421961114474293)
                ·
                  rfl

theorem cell19_266288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_266288 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_266288 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_266288 prefixEnd_266288 := by exact prefixLift 266288
  have htrace : WordTrace (prefixWord ++ tailWord_266288) baseStart_266288 baseEnd_266288 := by
    simpa [prefixWord, tailWord_266288, baseEnd_266288] using wordTrace_append hprefix tailTrace_266288
  have hstable : (prefixWord ++ tailWord_266288).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266288).length < 2 ^ (prefixWord ++ tailWord_266288).sum := by decide
  have hdescent : baseEnd_266288 < baseStart_266288 := by decide
  rcases family_descends (prefixWord ++ tailWord_266288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266305 : List Nat := [1, 2, 5, 1, 2, 1, 2, 5]
def baseStart_266305 : Nat := 118140960795 + 266305 * 2 ^ 59
def prefixEnd_266305 : Nat := 4983230072969 + 3 ^ 40 * 266305 * 2
def baseEnd_266305 : Nat := 81032572264110112096469

theorem tailTrace_266305 : CollatzResearch.WordTrace tailWord_266305 prefixEnd_266305 81032572264110112096469 := by
  unfold tailWord_266305
  simp only [CollatzResearch.WordTrace]
  refine ⟨9712941300229941118160369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6475294200153294078773579 9712941300229941118160369)
  ·
    refine ⟨7284705975172455838620277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9712941300229941118160369 7284705975172455838620277)
    ·
      refine ⟨682941185172417734870651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7284705975172455838620277 682941185172417734870651)
      ·
        refine ⟨1024411777758626602305977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682941185172417734870651 1024411777758626602305977)
        ·
          refine ⟨768308833318969951729483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1024411777758626602305977 768308833318969951729483)
          ·
            refine ⟨1152463249978454927594225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768308833318969951729483 1152463249978454927594225)
            ·
              refine ⟨864347437483841195695669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1152463249978454927594225 864347437483841195695669)
              ·
                refine ⟨81032572264110112096469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 864347437483841195695669 81032572264110112096469)
                ·
                  rfl

theorem cell19_266305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_266305 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_266305 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_266305 prefixEnd_266305 := by exact prefixLift 266305
  have htrace : WordTrace (prefixWord ++ tailWord_266305) baseStart_266305 baseEnd_266305 := by
    simpa [prefixWord, tailWord_266305, baseEnd_266305] using wordTrace_append hprefix tailTrace_266305
  have hstable : (prefixWord ++ tailWord_266305).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266305).length < 2 ^ (prefixWord ++ tailWord_266305).sum := by decide
  have hdescent : baseEnd_266305 < baseStart_266305 := by decide
  rcases family_descends (prefixWord ++ tailWord_266305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266434 : List Nat := [3, 5, 1, 1, 1, 3, 5]
def baseStart_266434 : Nat := 118140960795 + 266434 * 2 ^ 59
def prefixEnd_266434 : Nat := 4983230072969 + 3 ^ 40 * 266434 * 2
def baseEnd_266434 : Nat := 27023941669158678409817

theorem tailTrace_266434 : CollatzResearch.WordTrace tailWord_266434 prefixEnd_266434 27023941669158678409817 := by
  unfold tailWord_266434
  simp only [CollatzResearch.WordTrace]
  refine ⟨2429411579190649037401589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6478430877841730766404237 2429411579190649037401589)
  ·
    refine ⟨227757335549123347256399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2429411579190649037401589 227757335549123347256399)
    ·
      refine ⟨341636003323685020884599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227757335549123347256399 341636003323685020884599)
      ·
        refine ⟨512454004985527531326899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341636003323685020884599 512454004985527531326899)
        ·
          refine ⟨768681007478291296990349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512454004985527531326899 768681007478291296990349)
          ·
            refine ⟨288255377804359236371381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 768681007478291296990349 288255377804359236371381)
            ·
              refine ⟨27023941669158678409817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 288255377804359236371381 27023941669158678409817)
              ·
                rfl

theorem cell19_266434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 5].length) (baseStart_266434 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_266434 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_266434 prefixEnd_266434 := by exact prefixLift 266434
  have htrace : WordTrace (prefixWord ++ tailWord_266434) baseStart_266434 baseEnd_266434 := by
    simpa [prefixWord, tailWord_266434, baseEnd_266434] using wordTrace_append hprefix tailTrace_266434
  have hstable : (prefixWord ++ tailWord_266434).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266434).length < 2 ^ (prefixWord ++ tailWord_266434).sum := by decide
  have hdescent : baseEnd_266434 < baseStart_266434 := by decide
  rcases family_descends (prefixWord ++ tailWord_266434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266554 : List Nat := [3, 1, 1, 1, 4, 3, 6]
def baseStart_266554 : Nat := 118140960795 + 266554 * 2 ^ 59
def prefixEnd_266554 : Nat := 4983230072969 + 3 ^ 40 * 266554 * 2
def baseEnd_266554 : Nat := 27036113062450437520819

theorem tailTrace_266554 : CollatzResearch.WordTrace tailWord_266554 prefixEnd_266554 27036113062450437520819 := by
  unfold tailWord_266554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2430505769081964160993679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6481348717551904429316477 2430505769081964160993679)
  ·
    refine ⟨3645758653622946241490519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2430505769081964160993679 3645758653622946241490519)
    ·
      refine ⟨5468637980434419362235779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3645758653622946241490519 5468637980434419362235779)
      ·
        refine ⟨8202956970651629043353669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5468637980434419362235779 8202956970651629043353669)
        ·
          refine ⟨1538054431997180445628813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8202956970651629043353669 1538054431997180445628813)
          ·
            refine ⟨576770411998942667110805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1538054431997180445628813 576770411998942667110805)
            ·
              refine ⟨27036113062450437520819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 576770411998942667110805 27036113062450437520819)
              ·
                rfl

theorem cell19_266554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 6].length) (baseStart_266554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_266554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_266554 prefixEnd_266554 := by exact prefixLift 266554
  have htrace : WordTrace (prefixWord ++ tailWord_266554) baseStart_266554 baseEnd_266554 := by
    simpa [prefixWord, tailWord_266554, baseEnd_266554] using wordTrace_append hprefix tailTrace_266554
  have hstable : (prefixWord ++ tailWord_266554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266554).length < 2 ^ (prefixWord ++ tailWord_266554).sum := by decide
  have hdescent : baseEnd_266554 < baseStart_266554 := by decide
  rcases family_descends (prefixWord ++ tailWord_266554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266588 : List Nat := [2, 2, 4, 3, 1, 1, 1, 5]
def baseStart_266588 : Nat := 118140960795 + 266588 * 2 ^ 59
def prefixEnd_266588 : Nat := 4983230072969 + 3 ^ 40 * 266588 * 2
def baseEnd_266588 : Nat := 81118684871649307806809

theorem tailTrace_266588 : CollatzResearch.WordTrace tailWord_266588 prefixEnd_266588 81118684871649307806809 := by
  unfold tailWord_266588
  simp only [CollatzResearch.WordTrace]
  refine ⟨4861631579102340225356209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6482175438803120300474945 4861631579102340225356209)
  ·
    refine ⟨3646223684326755169017157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4861631579102340225356209 3646223684326755169017157)
    ·
      refine ⟨683666940811266594190717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3646223684326755169017157 683666940811266594190717)
      ·
        refine ⟨256375102804224972821519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 683666940811266594190717 256375102804224972821519)
        ·
          refine ⟨384562654206337459232279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256375102804224972821519 384562654206337459232279)
          ·
            refine ⟨576843981309506188848419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384562654206337459232279 576843981309506188848419)
            ·
              refine ⟨865265971964259283272629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576843981309506188848419 865265971964259283272629)
              ·
                refine ⟨81118684871649307806809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 865265971964259283272629 81118684871649307806809)
                ·
                  rfl

theorem cell19_266588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_266588 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_266588 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_266588 prefixEnd_266588 := by exact prefixLift 266588
  have htrace : WordTrace (prefixWord ++ tailWord_266588) baseStart_266588 baseEnd_266588 := by
    simpa [prefixWord, tailWord_266588, baseEnd_266588] using wordTrace_append hprefix tailTrace_266588
  have hstable : (prefixWord ++ tailWord_266588).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266588).length < 2 ^ (prefixWord ++ tailWord_266588).sum := by decide
  have hdescent : baseEnd_266588 < baseStart_266588 := by decide
  rcases family_descends (prefixWord ++ tailWord_266588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266685 : List Nat := [1, 4, 1, 2, 2, 4, 1, 4]
def baseStart_266685 : Nat := 118140960795 + 266685 * 2 ^ 59
def prefixEnd_266685 : Nat := 4983230072969 + 3 ^ 40 * 266685 * 2
def baseEnd_266685 : Nat := 81148200500381823650989

theorem tailTrace_266685 : CollatzResearch.WordTrace tailWord_266685 prefixEnd_266685 81148200500381823650989 := by
  unfold tailWord_266685
  simp only [CollatzResearch.WordTrace]
  refine ⟨9726801038853266016993509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6484534025902177344662339 9726801038853266016993509)
  ·
    refine ⟨1823775194784987378186283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9726801038853266016993509 1823775194784987378186283)
    ·
      refine ⟨2735662792177481067279425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1823775194784987378186283 2735662792177481067279425)
      ·
        refine ⟨2051747094133110800459569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2735662792177481067279425 2051747094133110800459569)
        ·
          refine ⟨1538810320599833100344677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2051747094133110800459569 1538810320599833100344677)
          ·
            refine ⟨288526935112468706314627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1538810320599833100344677 288526935112468706314627)
            ·
              refine ⟨432790402668703059471941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288526935112468706314627 432790402668703059471941)
              ·
                refine ⟨81148200500381823650989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 432790402668703059471941 81148200500381823650989)
                ·
                  rfl

theorem cell19_266685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 4].length) (baseStart_266685 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_266685 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_266685 prefixEnd_266685 := by exact prefixLift 266685
  have htrace : WordTrace (prefixWord ++ tailWord_266685) baseStart_266685 baseEnd_266685 := by
    simpa [prefixWord, tailWord_266685, baseEnd_266685] using wordTrace_append hprefix tailTrace_266685
  have hstable : (prefixWord ++ tailWord_266685).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266685).length < 2 ^ (prefixWord ++ tailWord_266685).sum := by decide
  have hdescent : baseEnd_266685 < baseStart_266685 := by decide
  rcases family_descends (prefixWord ++ tailWord_266685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266759 : List Nat := [1, 1, 4, 3, 3, 2, 2, 3]
def baseStart_266759 : Nat := 118140960795 + 266759 * 2 ^ 59
def prefixEnd_266759 : Nat := 4983230072969 + 3 ^ 40 * 266759 * 2
def baseEnd_266759 : Nat := 81170717577971578006343

theorem tailTrace_266759 : CollatzResearch.WordTrace tailWord_266759 prefixEnd_266759 81170717577971578006343 := by
  unfold tailWord_266759
  simp only [CollatzResearch.WordTrace]
  refine ⟨9729500040585176655187331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6486333360390117770124887 9729500040585176655187331)
  ·
    refine ⟨14594250060877764982780997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9729500040585176655187331 14594250060877764982780997)
    ·
      refine ⟨2736421886414580934271437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14594250060877764982780997 2736421886414580934271437)
      ·
        refine ⟨1026158207405467850351789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2736421886414580934271437 1026158207405467850351789)
        ·
          refine ⟨384809327777050443881921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1026158207405467850351789 384809327777050443881921)
          ·
            refine ⟨288606995832787832911441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384809327777050443881921 288606995832787832911441)
            ·
              refine ⟨216455246874590874683581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288606995832787832911441 216455246874590874683581)
              ·
                refine ⟨81170717577971578006343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216455246874590874683581 81170717577971578006343)
                ·
                  rfl

theorem cell19_266759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 3].length) (baseStart_266759 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_266759 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_266759 prefixEnd_266759 := by exact prefixLift 266759
  have htrace : WordTrace (prefixWord ++ tailWord_266759) baseStart_266759 baseEnd_266759 := by
    simpa [prefixWord, tailWord_266759, baseEnd_266759] using wordTrace_append hprefix tailTrace_266759
  have hstable : (prefixWord ++ tailWord_266759).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266759).length < 2 ^ (prefixWord ++ tailWord_266759).sum := by decide
  have hdescent : baseEnd_266759 < baseStart_266759 := by decide
  rcases family_descends (prefixWord ++ tailWord_266759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266763 : List Nat := [1, 1, 1, 1, 7, 2, 1, 5]
def baseStart_266763 : Nat := 118140960795 + 266763 * 2 ^ 59
def prefixEnd_266763 : Nat := 4983230072969 + 3 ^ 40 * 266763 * 2
def baseEnd_266763 : Nat := 81171934717300753917443

theorem tailTrace_266763 : CollatzResearch.WordTrace tailWord_266763 prefixEnd_266763 81171934717300753917443 := by
  unfold tailWord_266763
  simp only [CollatzResearch.WordTrace]
  refine ⟨9729645932570685338332943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6486430621713790225555295 9729645932570685338332943)
  ·
    refine ⟨14594468898856028007499415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9729645932570685338332943 14594468898856028007499415)
    ·
      refine ⟨21891703348284042011249123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14594468898856028007499415 21891703348284042011249123)
      ·
        refine ⟨32837555022426063016873685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21891703348284042011249123 32837555022426063016873685)
        ·
          refine ⟨769630195838110851957977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 32837555022426063016873685 769630195838110851957977)
          ·
            refine ⟨577222646878583138968483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769630195838110851957977 577222646878583138968483)
            ·
              refine ⟨865833970317874708452725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577222646878583138968483 865833970317874708452725)
              ·
                refine ⟨81171934717300753917443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 865833970317874708452725 81171934717300753917443)
                ·
                  rfl

theorem cell19_266763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_266763 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_266763 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_266763 prefixEnd_266763 := by exact prefixLift 266763
  have htrace : WordTrace (prefixWord ++ tailWord_266763) baseStart_266763 baseEnd_266763 := by
    simpa [prefixWord, tailWord_266763, baseEnd_266763] using wordTrace_append hprefix tailTrace_266763
  have hstable : (prefixWord ++ tailWord_266763).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266763).length < 2 ^ (prefixWord ++ tailWord_266763).sum := by decide
  have hdescent : baseEnd_266763 < baseStart_266763 := by decide
  rcases family_descends (prefixWord ++ tailWord_266763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266917 : List Nat := [1, 3, 1, 2, 1, 2, 1, 8]
def baseStart_266917 : Nat := 118140960795 + 266917 * 2 ^ 59
def prefixEnd_266917 : Nat := 4983230072969 + 3 ^ 40 * 266917 * 2
def baseEnd_266917 : Nat := 81218794581474026494801

theorem tailTrace_266917 : CollatzResearch.WordTrace tailWord_266917 prefixEnd_266917 81218794581474026494801 := by
  unfold tailWord_266917
  simp only [CollatzResearch.WordTrace]
  refine ⟨9735262774012769639439005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6490175182675179759626003 9735262774012769639439005)
  ·
    refine ⟨3650723540254788614789627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9735262774012769639439005 3650723540254788614789627)
    ·
      refine ⟨5476085310382182922184441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3650723540254788614789627 5476085310382182922184441)
      ·
        refine ⟨4107063982786637191638331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5476085310382182922184441 4107063982786637191638331)
        ·
          refine ⟨6160595974179955787457497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4107063982786637191638331 6160595974179955787457497)
          ·
            refine ⟨4620446980634966840593123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6160595974179955787457497 4620446980634966840593123)
            ·
              refine ⟨6930670470952450260889685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4620446980634966840593123 6930670470952450260889685)
              ·
                refine ⟨81218794581474026494801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6930670470952450260889685 81218794581474026494801)
                ·
                  rfl

theorem cell19_266917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_266917 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_266917 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_266917 prefixEnd_266917 := by exact prefixLift 266917
  have htrace : WordTrace (prefixWord ++ tailWord_266917) baseStart_266917 baseEnd_266917 := by
    simpa [prefixWord, tailWord_266917, baseEnd_266917] using wordTrace_append hprefix tailTrace_266917
  have hstable : (prefixWord ++ tailWord_266917).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266917).length < 2 ^ (prefixWord ++ tailWord_266917).sum := by decide
  have hdescent : baseEnd_266917 < baseStart_266917 := by decide
  rcases family_descends (prefixWord ++ tailWord_266917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266993 : List Nat := [1, 2, 2, 2, 2, 2, 1, 7]
def baseStart_266993 : Nat := 118140960795 + 266993 * 2 ^ 59
def prefixEnd_266993 : Nat := 4983230072969 + 3 ^ 40 * 266993 * 2
def baseEnd_266993 : Nat := 81241920228728368805705

theorem tailTrace_266993 : CollatzResearch.WordTrace tailWord_266993 prefixEnd_266993 81241920228728368805705 := by
  unfold tailWord_266993
  simp only [CollatzResearch.WordTrace]
  refine ⟨9738034721737434619205633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6492023147824956412803755 9738034721737434619205633)
  ·
    refine ⟨7303526041303075964404225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9738034721737434619205633 7303526041303075964404225)
    ·
      refine ⟨5477644530977306973303169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7303526041303075964404225 5477644530977306973303169)
      ·
        refine ⟨4108233398232980229977377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5477644530977306973303169 4108233398232980229977377)
        ·
          refine ⟨3081175048674735172483033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4108233398232980229977377 3081175048674735172483033)
          ·
            refine ⟨2310881286506051379362275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3081175048674735172483033 2310881286506051379362275)
            ·
              refine ⟨3466321929759077069043413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2310881286506051379362275 3466321929759077069043413)
              ·
                refine ⟨81241920228728368805705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3466321929759077069043413 81241920228728368805705)
                ·
                  rfl

theorem cell19_266993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_266993 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_266993 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_266993 prefixEnd_266993 := by exact prefixLift 266993
  have htrace : WordTrace (prefixWord ++ tailWord_266993) baseStart_266993 baseEnd_266993 := by
    simpa [prefixWord, tailWord_266993, baseEnd_266993] using wordTrace_append hprefix tailTrace_266993
  have hstable : (prefixWord ++ tailWord_266993).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266993).length < 2 ^ (prefixWord ++ tailWord_266993).sum := by decide
  have hdescent : baseEnd_266993 < baseStart_266993 := by decide
  rcases family_descends (prefixWord ++ tailWord_266993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267010 : List Nat := [3, 4, 1, 1, 1, 9]
def baseStart_267010 : Nat := 118140960795 + 267010 * 2 ^ 59
def prefixEnd_267010 : Nat := 4983230072969 + 3 ^ 40 * 267010 * 2
def baseEnd_267010 : Nat := 9027454785653040714209

theorem tailTrace_267010 : CollatzResearch.WordTrace tailWord_267010 prefixEnd_267010 9027454785653040714209 := by
  unfold tailWord_267010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2434663690668961630643621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6492436508450564348382989 2434663690668961630643621)
  ·
    refine ⟨456499442000430305745679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2434663690668961630643621 456499442000430305745679)
    ·
      refine ⟨684749163000645458618519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456499442000430305745679 684749163000645458618519)
      ·
        refine ⟨1027123744500968187927779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684749163000645458618519 1027123744500968187927779)
        ·
          refine ⟨1540685616751452281891669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027123744500968187927779 1540685616751452281891669)
          ·
            refine ⟨9027454785653040714209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1540685616751452281891669 9027454785653040714209)
            ·
              rfl

theorem cell19_267010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 9].length) (baseStart_267010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267010 prefixEnd_267010 := by exact prefixLift 267010
  have htrace : WordTrace (prefixWord ++ tailWord_267010) baseStart_267010 baseEnd_267010 := by
    simpa [prefixWord, tailWord_267010, baseEnd_267010] using wordTrace_append hprefix tailTrace_267010
  have hstable : (prefixWord ++ tailWord_267010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267010).length < 2 ^ (prefixWord ++ tailWord_267010).sum := by decide
  have hdescent : baseEnd_267010 < baseStart_267010 := by decide
  rcases family_descends (prefixWord ++ tailWord_267010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267143 : List Nat := [1, 1, 4, 2, 3, 2, 2, 4]
def baseStart_267143 : Nat := 118140960795 + 267143 * 2 ^ 59
def prefixEnd_267143 : Nat := 4983230072969 + 3 ^ 40 * 267143 * 2
def baseEnd_267143 : Nat := 81287562953572465471963

theorem tailTrace_267143 : CollatzResearch.WordTrace tailWord_267143 prefixEnd_267143 81287562953572465471963 := by
  unfold tailWord_267143
  simp only [CollatzResearch.WordTrace]
  refine ⟨9743505671194010237166083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6495670447462673491444055 9743505671194010237166083)
  ·
    refine ⟨14615258506791015355749125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9743505671194010237166083 14615258506791015355749125)
    ·
      refine ⟨2740360970023315379202961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14615258506791015355749125 2740360970023315379202961)
      ·
        refine ⟨2055270727517486534402221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2740360970023315379202961 2055270727517486534402221)
        ·
          refine ⟨770726522819057450400833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2055270727517486534402221 770726522819057450400833)
          ·
            refine ⟨578044892114293087800625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 770726522819057450400833 578044892114293087800625)
            ·
              refine ⟨433533669085719815850469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578044892114293087800625 433533669085719815850469)
              ·
                refine ⟨81287562953572465471963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 433533669085719815850469 81287562953572465471963)
                ·
                  rfl

theorem cell19_267143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_267143 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267143 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267143 prefixEnd_267143 := by exact prefixLift 267143
  have htrace : WordTrace (prefixWord ++ tailWord_267143) baseStart_267143 baseEnd_267143 := by
    simpa [prefixWord, tailWord_267143, baseEnd_267143] using wordTrace_append hprefix tailTrace_267143
  have hstable : (prefixWord ++ tailWord_267143).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267143).length < 2 ^ (prefixWord ++ tailWord_267143).sum := by decide
  have hdescent : baseEnd_267143 < baseStart_267143 := by decide
  rcases family_descends (prefixWord ++ tailWord_267143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267145 : List Nat := [1, 2, 1, 1, 5, 2, 1, 6]
def baseStart_267145 : Nat := 118140960795 + 267145 * 2 ^ 59
def prefixEnd_267145 : Nat := 4983230072969 + 3 ^ 40 * 267145 * 2
def baseEnd_267145 : Nat := 81288171523237053427513

theorem tailTrace_267145 : CollatzResearch.WordTrace tailWord_267145 prefixEnd_267145 81288171523237053427513 := by
  unfold tailWord_267145
  simp only [CollatzResearch.WordTrace]
  refine ⟨9743578617186764578738889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6495719078124509719159259 9743578617186764578738889)
  ·
    refine ⟨7307683962890073434054167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9743578617186764578738889 7307683962890073434054167)
    ·
      refine ⟨10961525944335110151081251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7307683962890073434054167 10961525944335110151081251)
      ·
        refine ⟨16442288916502665226621877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10961525944335110151081251 16442288916502665226621877)
        ·
          refine ⟨1541464585922124864995801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16442288916502665226621877 1541464585922124864995801)
          ·
            refine ⟨1156098439441593648746851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1541464585922124864995801 1156098439441593648746851)
            ·
              refine ⟨1734147659162390473120277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1156098439441593648746851 1734147659162390473120277)
              ·
                refine ⟨81288171523237053427513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1734147659162390473120277 81288171523237053427513)
                ·
                  rfl

theorem cell19_267145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_267145 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267145 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267145 prefixEnd_267145 := by exact prefixLift 267145
  have htrace : WordTrace (prefixWord ++ tailWord_267145) baseStart_267145 baseEnd_267145 := by
    simpa [prefixWord, tailWord_267145, baseEnd_267145] using wordTrace_append hprefix tailTrace_267145
  have hstable : (prefixWord ++ tailWord_267145).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267145).length < 2 ^ (prefixWord ++ tailWord_267145).sum := by decide
  have hdescent : baseEnd_267145 < baseStart_267145 := by decide
  rcases family_descends (prefixWord ++ tailWord_267145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267158 : List Nat := [5, 3, 1, 1, 1, 1, 2, 5]
def baseStart_267158 : Nat := 118140960795 + 267158 * 2 ^ 59
def prefixEnd_267158 : Nat := 4983230072969 + 3 ^ 40 * 267158 * 2
def baseEnd_267158 : Nat := 81292127226056875138589

theorem tailTrace_267158 : CollatzResearch.WordTrace tailWord_267158 prefixEnd_267158 81292127226056875138589 := by
  unfold tailWord_267158
  simp only [CollatzResearch.WordTrace]
  refine ⟨609003297883729237435133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6496035177426445199308085 609003297883729237435133)
  ·
    refine ⟨228376236706398464038175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 609003297883729237435133 228376236706398464038175)
    ·
      refine ⟨342564355059597696057263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228376236706398464038175 342564355059597696057263)
      ·
        refine ⟨513846532589396544085895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342564355059597696057263 513846532589396544085895)
        ·
          refine ⟨770769798884094816128843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513846532589396544085895 770769798884094816128843)
          ·
            refine ⟨1156154698326142224193265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770769798884094816128843 1156154698326142224193265)
            ·
              refine ⟨867116023744606668144949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1156154698326142224193265 867116023744606668144949)
              ·
                refine ⟨81292127226056875138589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 867116023744606668144949 81292127226056875138589)
                ·
                  rfl

theorem cell19_267158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_267158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267158 prefixEnd_267158 := by exact prefixLift 267158
  have htrace : WordTrace (prefixWord ++ tailWord_267158) baseStart_267158 baseEnd_267158 := by
    simpa [prefixWord, tailWord_267158, baseEnd_267158] using wordTrace_append hprefix tailTrace_267158
  have hstable : (prefixWord ++ tailWord_267158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267158).length < 2 ^ (prefixWord ++ tailWord_267158).sum := by decide
  have hdescent : baseEnd_267158 < baseStart_267158 := by decide
  rcases family_descends (prefixWord ++ tailWord_267158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267181 : List Nat := [1, 5, 2, 3, 8]
def baseStart_267181 : Nat := 118140960795 + 267181 * 2 ^ 59
def prefixEnd_267181 : Nat := 4983230072969 + 3 ^ 40 * 267181 * 2
def baseEnd_267181 : Nat := 3011078732488875430645

theorem tailTrace_267181 : CollatzResearch.WordTrace tailWord_267181 prefixEnd_267181 3011078732488875430645 := by
  unfold tailWord_267181
  simp only [CollatzResearch.WordTrace]
  refine ⟨9744891645056342727049397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6496594430037561818032931 9744891645056342727049397)
  ·
    refine ⟨913583591724032130660881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9744891645056342727049397 913583591724032130660881)
    ·
      refine ⟨685187693793024097995661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 913583591724032130660881 685187693793024097995661)
      ·
        refine ⟨256945385172384036748373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 685187693793024097995661 256945385172384036748373)
        ·
          refine ⟨3011078732488875430645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 256945385172384036748373 3011078732488875430645)
          ·
            rfl

theorem cell19_267181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 8].length) (baseStart_267181 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267181 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267181 prefixEnd_267181 := by exact prefixLift 267181
  have htrace : WordTrace (prefixWord ++ tailWord_267181) baseStart_267181 baseEnd_267181 := by
    simpa [prefixWord, tailWord_267181, baseEnd_267181] using wordTrace_append hprefix tailTrace_267181
  have hstable : (prefixWord ++ tailWord_267181).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267181).length < 2 ^ (prefixWord ++ tailWord_267181).sum := by decide
  have hdescent : baseEnd_267181 < baseStart_267181 := by decide
  rcases family_descends (prefixWord ++ tailWord_267181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267200 : List Nat := [2, 1, 1, 2, 3, 5, 1, 4]
def baseStart_267200 : Nat := 118140960795 + 267200 * 2 ^ 59
def prefixEnd_267200 : Nat := 4983230072969 + 3 ^ 40 * 267200 * 2
def baseEnd_267200 : Nat := 81304907189013222205141

theorem tailTrace_267200 : CollatzResearch.WordTrace tailWord_267200 prefixEnd_267200 81304907189013222205141 := by
  unfold tailWord_267200
  simp only [CollatzResearch.WordTrace]
  refine ⟨4872792315993754485995527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6497056421325005981327369 4872792315993754485995527)
  ·
    refine ⟨7309188473990631728993291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4872792315993754485995527 7309188473990631728993291)
    ·
      refine ⟨10963782710985947593489937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7309188473990631728993291 10963782710985947593489937)
      ·
        refine ⟨8222837033239460695117453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10963782710985947593489937 8222837033239460695117453)
        ·
          refine ⟨3083563887464797760669045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8222837033239460695117453 3083563887464797760669045)
          ·
            refine ⟨289084114449824790062723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3083563887464797760669045 289084114449824790062723)
            ·
              refine ⟨433626171674737185094085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289084114449824790062723 433626171674737185094085)
              ·
                refine ⟨81304907189013222205141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 433626171674737185094085 81304907189013222205141)
                ·
                  rfl

theorem cell19_267200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_267200 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267200 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267200 prefixEnd_267200 := by exact prefixLift 267200
  have htrace : WordTrace (prefixWord ++ tailWord_267200) baseStart_267200 baseEnd_267200 := by
    simpa [prefixWord, tailWord_267200, baseEnd_267200] using wordTrace_append hprefix tailTrace_267200
  have hstable : (prefixWord ++ tailWord_267200).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267200).length < 2 ^ (prefixWord ++ tailWord_267200).sum := by decide
  have hdescent : baseEnd_267200 < baseStart_267200 := by decide
  rcases family_descends (prefixWord ++ tailWord_267200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267274 : List Nat := [3, 1, 2, 2, 3, 3, 2, 3]
def baseStart_267274 : Nat := 118140960795 + 267274 * 2 ^ 59
def prefixEnd_267274 : Nat := 4983230072969 + 3 ^ 40 * 267274 * 2
def baseEnd_267274 : Nat := 81327424266602976560495

theorem tailTrace_267274 : CollatzResearch.WordTrace tailWord_267274 prefixEnd_267274 81327424266602976560495 := by
  unfold tailWord_267274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2437070908429854902546219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6498855755812946406789917 2437070908429854902546219)
  ·
    refine ⟨3655606362644782353819329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2437070908429854902546219 3655606362644782353819329)
    ·
      refine ⟨2741704771983586765364497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3655606362644782353819329 2741704771983586765364497)
      ·
        refine ⟨2056278578987690074023373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2741704771983586765364497 2056278578987690074023373)
        ·
          refine ⟨771104467120383777758765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2056278578987690074023373 771104467120383777758765)
          ·
            refine ⟨289164175170143916659537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 771104467120383777758765 289164175170143916659537)
            ·
              refine ⟨216873131377607937494653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289164175170143916659537 216873131377607937494653)
              ·
                refine ⟨81327424266602976560495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216873131377607937494653 81327424266602976560495)
                ·
                  rfl

theorem cell19_267274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_267274 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267274 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267274 prefixEnd_267274 := by exact prefixLift 267274
  have htrace : WordTrace (prefixWord ++ tailWord_267274) baseStart_267274 baseEnd_267274 := by
    simpa [prefixWord, tailWord_267274, baseEnd_267274] using wordTrace_append hprefix tailTrace_267274
  have hstable : (prefixWord ++ tailWord_267274).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267274).length < 2 ^ (prefixWord ++ tailWord_267274).sum := by decide
  have hdescent : baseEnd_267274 < baseStart_267274 := by decide
  rcases family_descends (prefixWord ++ tailWord_267274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267276 : List Nat := [2, 2, 1, 2, 3, 2, 4, 3]
def baseStart_267276 : Nat := 118140960795 + 267276 * 2 ^ 59
def prefixEnd_267276 : Nat := 4983230072969 + 3 ^ 40 * 267276 * 2
def baseEnd_267276 : Nat := 81328032836267564516045

theorem tailTrace_267276 : CollatzResearch.WordTrace tailWord_267276 prefixEnd_267276 81328032836267564516045 := by
  unfold tailWord_267276
  simp only [CollatzResearch.WordTrace]
  refine ⟨4874178289856086975878841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6498904386474782634505121 4874178289856086975878841)
  ·
    refine ⟨3655633717392065231909131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4874178289856086975878841 3655633717392065231909131)
    ·
      refine ⟨5483450576088097847863697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3655633717392065231909131 5483450576088097847863697)
      ·
        refine ⟨4112587932066073385897773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5483450576088097847863697 4112587932066073385897773)
        ·
          refine ⟨1542220474524777519711665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4112587932066073385897773 1542220474524777519711665)
          ·
            refine ⟨1156665355893583139783749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1542220474524777519711665 1156665355893583139783749)
            ·
              refine ⟨216874754230046838709453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1156665355893583139783749 216874754230046838709453)
              ·
                refine ⟨81328032836267564516045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216874754230046838709453 81328032836267564516045)
                ·
                  rfl

theorem cell19_267276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_267276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267276 prefixEnd_267276 := by exact prefixLift 267276
  have htrace : WordTrace (prefixWord ++ tailWord_267276) baseStart_267276 baseEnd_267276 := by
    simpa [prefixWord, tailWord_267276, baseEnd_267276] using wordTrace_append hprefix tailTrace_267276
  have hstable : (prefixWord ++ tailWord_267276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267276).length < 2 ^ (prefixWord ++ tailWord_267276).sum := by decide
  have hdescent : baseEnd_267276 < baseStart_267276 := by decide
  rcases family_descends (prefixWord ++ tailWord_267276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267293 : List Nat := [1, 4, 2, 2, 4, 1, 5]
def baseStart_267293 : Nat := 118140960795 + 267293 * 2 ^ 59
def prefixEnd_267293 : Nat := 4983230072969 + 3 ^ 40 * 267293 * 2
def baseEnd_267293 : Nat := 27111068559472187379407

theorem tailTrace_267293 : CollatzResearch.WordTrace tailWord_267293 prefixEnd_267293 27111068559472187379407 := by
  unfold tailWord_267293
  simp only [CollatzResearch.WordTrace]
  refine ⟨9748976620650585855126533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6499317747100390570084355 9748976620650585855126533)
  ·
    refine ⟨1827933116371984847836225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9748976620650585855126533 1827933116371984847836225)
    ·
      refine ⟨1370949837278988635877169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1827933116371984847836225 1370949837278988635877169)
      ·
        refine ⟨1028212377959241476907877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1370949837278988635877169 1028212377959241476907877)
        ·
          refine ⟨192789820867357776920227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1028212377959241476907877 192789820867357776920227)
          ·
            refine ⟨289184731301036665380341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192789820867357776920227 289184731301036665380341)
            ·
              refine ⟨27111068559472187379407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 289184731301036665380341 27111068559472187379407)
              ·
                rfl

theorem cell19_267293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 5].length) (baseStart_267293 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267293 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267293 prefixEnd_267293 := by exact prefixLift 267293
  have htrace : WordTrace (prefixWord ++ tailWord_267293) baseStart_267293 baseEnd_267293 := by
    simpa [prefixWord, tailWord_267293, baseEnd_267293] using wordTrace_append hprefix tailTrace_267293
  have hstable : (prefixWord ++ tailWord_267293).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267293).length < 2 ^ (prefixWord ++ tailWord_267293).sum := by decide
  have hdescent : baseEnd_267293 < baseStart_267293 := by decide
  rcases family_descends (prefixWord ++ tailWord_267293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267297 : List Nat := [1, 2, 3, 2, 3, 1, 7]
def baseStart_267297 : Nat := 118140960795 + 267297 * 2 ^ 59
def prefixEnd_267297 : Nat := 4983230072969 + 3 ^ 40 * 267297 * 2
def baseEnd_267297 : Nat := 27111474272581912683107

theorem tailTrace_267297 : CollatzResearch.WordTrace tailWord_267297 prefixEnd_267297 27111474272581912683107 := by
  unfold tailWord_267297
  simp only [CollatzResearch.WordTrace]
  refine ⟨9749122512636094538272145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6499415008424063025514763 9749122512636094538272145)
  ·
    refine ⟨7311841884477070903704109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9749122512636094538272145 7311841884477070903704109)
    ·
      refine ⟨2741940706678901588889041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7311841884477070903704109 2741940706678901588889041)
      ·
        refine ⟨2056455530009176191666781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2741940706678901588889041 2056455530009176191666781)
        ·
          refine ⟨771170823753441071875043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2056455530009176191666781 771170823753441071875043)
          ·
            refine ⟨1156756235630161607812565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771170823753441071875043 1156756235630161607812565)
            ·
              refine ⟨27111474272581912683107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1156756235630161607812565 27111474272581912683107)
              ·
                rfl

theorem cell19_267297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 7].length) (baseStart_267297 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267297 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267297 prefixEnd_267297 := by exact prefixLift 267297
  have htrace : WordTrace (prefixWord ++ tailWord_267297) baseStart_267297 baseEnd_267297 := by
    simpa [prefixWord, tailWord_267297, baseEnd_267297] using wordTrace_append hprefix tailTrace_267297
  have hstable : (prefixWord ++ tailWord_267297).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267297).length < 2 ^ (prefixWord ++ tailWord_267297).sum := by decide
  have hdescent : baseEnd_267297 < baseStart_267297 := by decide
  rcases family_descends (prefixWord ++ tailWord_267297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267335 : List Nat := [1, 1, 4, 1, 3, 2, 2, 5]
def baseStart_267335 : Nat := 118140960795 + 267335 * 2 ^ 59
def prefixEnd_267335 : Nat := 4983230072969 + 3 ^ 40 * 267335 * 2
def baseEnd_267335 : Nat := 81345985641372909204773

theorem tailTrace_267335 : CollatzResearch.WordTrace tailWord_267335 prefixEnd_267335 81345985641372909204773 := by
  unfold tailWord_267335
  simp only [CollatzResearch.WordTrace]
  refine ⟨9750508486498427028155459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6500338990998951352103639 9750508486498427028155459)
  ·
    refine ⟨14625762729747640542233189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9750508486498427028155459 14625762729747640542233189)
    ·
      refine ⟨2742330511827682601668723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14625762729747640542233189 2742330511827682601668723)
      ·
        refine ⟨4113495767741523902503085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2742330511827682601668723 4113495767741523902503085)
        ·
          refine ⟨1542560912903071463438657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4113495767741523902503085 1542560912903071463438657)
          ·
            refine ⟨1156920684677303597578993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1542560912903071463438657 1156920684677303597578993)
            ·
              refine ⟨867690513507977698184245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1156920684677303597578993 867690513507977698184245)
              ·
                refine ⟨81345985641372909204773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 867690513507977698184245 81345985641372909204773)
                ·
                  rfl

theorem cell19_267335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_267335 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267335 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267335 prefixEnd_267335 := by exact prefixLift 267335
  have htrace : WordTrace (prefixWord ++ tailWord_267335) baseStart_267335 baseEnd_267335 := by
    simpa [prefixWord, tailWord_267335, baseEnd_267335] using wordTrace_append hprefix tailTrace_267335
  have hstable : (prefixWord ++ tailWord_267335).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267335).length < 2 ^ (prefixWord ++ tailWord_267335).sum := by decide
  have hdescent : baseEnd_267335 < baseStart_267335 := by decide
  rcases family_descends (prefixWord ++ tailWord_267335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267350 : List Nat := [5, 2, 2, 1, 2, 7]
def baseStart_267350 : Nat := 118140960795 + 267350 * 2 ^ 59
def prefixEnd_267350 : Nat := 4983230072969 + 3 ^ 40 * 267350 * 2
def baseEnd_267350 : Nat := 9038949990428590985711

theorem tailTrace_267350 : CollatzResearch.WordTrace tailWord_267350 prefixEnd_267350 9038949990428590985711 := by
  unfold tailWord_267350
  simp only [CollatzResearch.WordTrace]
  refine ⟨609440973840255286871969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6500703720962723059967669 609440973840255286871969)
  ·
    refine ⟨457080730380191465153977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 609440973840255286871969 457080730380191465153977)
    ·
      refine ⟨342810547785143598865483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457080730380191465153977 342810547785143598865483)
      ·
        refine ⟨514215821677715398298225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342810547785143598865483 514215821677715398298225)
        ·
          refine ⟨385661866258286548723669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514215821677715398298225 385661866258286548723669)
          ·
            refine ⟨9038949990428590985711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 385661866258286548723669 9038949990428590985711)
            ·
              rfl

theorem cell19_267350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 7].length) (baseStart_267350 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267350 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267350 prefixEnd_267350 := by exact prefixLift 267350
  have htrace : WordTrace (prefixWord ++ tailWord_267350) baseStart_267350 baseEnd_267350 := by
    simpa [prefixWord, tailWord_267350, baseEnd_267350] using wordTrace_append hprefix tailTrace_267350
  have hstable : (prefixWord ++ tailWord_267350).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267350).length < 2 ^ (prefixWord ++ tailWord_267350).sum := by decide
  have hdescent : baseEnd_267350 < baseStart_267350 := by decide
  rcases family_descends (prefixWord ++ tailWord_267350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267449 : List Nat := [1, 2, 1, 4, 1, 4, 1, 5]
def baseStart_267449 : Nat := 118140960795 + 267449 * 2 ^ 59
def prefixEnd_267449 : Nat := 4983230072969 + 3 ^ 40 * 267449 * 2
def baseEnd_267449 : Nat := 81380674112254422671129

theorem tailTrace_267449 : CollatzResearch.WordTrace tailWord_267449 prefixEnd_267449 81380674112254422671129 := by
  unfold tailWord_267449
  simp only [CollatzResearch.WordTrace]
  refine ⟨9754666408085424497805401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6503110938723616331870267 9754666408085424497805401)
  ·
    refine ⟨7315999806064068373354051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9754666408085424497805401 7315999806064068373354051)
    ·
      refine ⟨10973999709096102560031077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7315999806064068373354051 10973999709096102560031077)
      ·
        refine ⟨2057624945455519230005827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10973999709096102560031077 2057624945455519230005827)
        ·
          refine ⟨3086437418183278845008741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2057624945455519230005827 3086437418183278845008741)
          ·
            refine ⟨578707015909364783439139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3086437418183278845008741 578707015909364783439139)
            ·
              refine ⟨868060523864047175158709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578707015909364783439139 868060523864047175158709)
              ·
                refine ⟨81380674112254422671129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 868060523864047175158709 81380674112254422671129)
                ·
                  rfl

theorem cell19_267449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_267449 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267449 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267449 prefixEnd_267449 := by exact prefixLift 267449
  have htrace : WordTrace (prefixWord ++ tailWord_267449) baseStart_267449 baseEnd_267449 := by
    simpa [prefixWord, tailWord_267449, baseEnd_267449] using wordTrace_append hprefix tailTrace_267449
  have hstable : (prefixWord ++ tailWord_267449).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267449).length < 2 ^ (prefixWord ++ tailWord_267449).sum := by decide
  have hdescent : baseEnd_267449 < baseStart_267449 := by decide
  rcases family_descends (prefixWord ++ tailWord_267449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267527 : List Nat := [1, 1, 4, 13]
def baseStart_267527 : Nat := 118140960795 + 267527 * 2 ^ 59
def prefixEnd_267527 : Nat := 4983230072969 + 3 ^ 40 * 267527 * 2
def baseEnd_267527 : Nat := 1004992695421893246143

theorem tailTrace_267527 : CollatzResearch.WordTrace tailWord_267527 prefixEnd_267527 1004992695421893246143 := by
  unfold tailWord_267527
  simp only [CollatzResearch.WordTrace]
  refine ⟨9757511301802843819144835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6505007534535229212763223 9757511301802843819144835)
  ·
    refine ⟨14636266952704265728717253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9757511301802843819144835 14636266952704265728717253)
    ·
      refine ⟨2744300053632049824134485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14636266952704265728717253 2744300053632049824134485)
      ·
        refine ⟨1004992695421893246143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 2744300053632049824134485 1004992695421893246143)
        ·
          rfl

theorem cell19_267527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 13].length) (baseStart_267527 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267527 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267527 prefixEnd_267527 := by exact prefixLift 267527
  have htrace : WordTrace (prefixWord ++ tailWord_267527) baseStart_267527 baseEnd_267527 := by
    simpa [prefixWord, tailWord_267527, baseEnd_267527] using wordTrace_append hprefix tailTrace_267527
  have hstable : (prefixWord ++ tailWord_267527).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267527).length < 2 ^ (prefixWord ++ tailWord_267527).sum := by decide
  have hdescent : baseEnd_267527 < baseStart_267527 := by decide
  rcases family_descends (prefixWord ++ tailWord_267527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267538 : List Nat := [3, 2, 4, 2, 1, 2, 1, 4]
def baseStart_267538 : Nat := 118140960795 + 267538 * 2 ^ 59
def prefixEnd_267538 : Nat := 4983230072969 + 3 ^ 40 * 267538 * 2
def baseEnd_267538 : Nat := 81407755462328586693109

theorem tailTrace_267538 : CollatzResearch.WordTrace tailWord_267538 prefixEnd_267538 81407755462328586693109 := by
  unfold tailWord_267538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2439478126190748174448817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6505275003175328465196845 2439478126190748174448817)
  ·
    refine ⟨1829608594643061130836613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2439478126190748174448817 1829608594643061130836613)
    ·
      refine ⟨343051611495573962031865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1829608594643061130836613 343051611495573962031865)
      ·
        refine ⟨257288708621680471523899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343051611495573962031865 257288708621680471523899)
        ·
          refine ⟨385933062932520707285849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257288708621680471523899 385933062932520707285849)
          ·
            refine ⟨289449797199390530464387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385933062932520707285849 289449797199390530464387)
            ·
              refine ⟨434174695799085795696581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289449797199390530464387 434174695799085795696581)
              ·
                refine ⟨81407755462328586693109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 434174695799085795696581 81407755462328586693109)
                ·
                  rfl

theorem cell19_267538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_267538 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267538 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267538 prefixEnd_267538 := by exact prefixLift 267538
  have htrace : WordTrace (prefixWord ++ tailWord_267538) baseStart_267538 baseEnd_267538 := by
    simpa [prefixWord, tailWord_267538, baseEnd_267538] using wordTrace_append hprefix tailTrace_267538
  have hstable : (prefixWord ++ tailWord_267538).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267538).length < 2 ^ (prefixWord ++ tailWord_267538).sum := by decide
  have hdescent : baseEnd_267538 < baseStart_267538 := by decide
  rcases family_descends (prefixWord ++ tailWord_267538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267544 : List Nat := [2, 1, 2, 3, 1, 3, 3, 4]
def baseStart_267544 : Nat := 118140960795 + 267544 * 2 ^ 59
def prefixEnd_267544 : Nat := 4983230072969 + 3 ^ 40 * 267544 * 2
def baseEnd_267544 : Nat := 81409581171322350559759

theorem tailTrace_267544 : CollatzResearch.WordTrace tailWord_267544 prefixEnd_267544 81409581171322350559759 := by
  unfold tailWord_267544
  simp only [CollatzResearch.WordTrace]
  refine ⟨4879065671370627861256843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6505420895160837148342457 4879065671370627861256843)
  ·
    refine ⟨7318598507055941791885265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4879065671370627861256843 7318598507055941791885265)
    ·
      refine ⟨5488948880291956343913949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7318598507055941791885265 5488948880291956343913949)
      ·
        refine ⟨2058355830109483628967731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5488948880291956343913949 2058355830109483628967731)
        ·
          refine ⟨3087533745164225443451597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058355830109483628967731 3087533745164225443451597)
          ·
            refine ⟨1157825154436584541294349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3087533745164225443451597 1157825154436584541294349)
            ·
              refine ⟨434184432913719202985381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1157825154436584541294349 434184432913719202985381)
              ·
                refine ⟨81409581171322350559759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 434184432913719202985381 81409581171322350559759)
                ·
                  rfl

theorem cell19_267544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_267544 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267544 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267544 prefixEnd_267544 := by exact prefixLift 267544
  have htrace : WordTrace (prefixWord ++ tailWord_267544) baseStart_267544 baseEnd_267544 := by
    simpa [prefixWord, tailWord_267544, baseEnd_267544] using wordTrace_append hprefix tailTrace_267544
  have hstable : (prefixWord ++ tailWord_267544).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267544).length < 2 ^ (prefixWord ++ tailWord_267544).sum := by decide
  have hdescent : baseEnd_267544 < baseStart_267544 := by decide
  rcases family_descends (prefixWord ++ tailWord_267544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267582 : List Nat := [4, 2, 1, 2, 1, 1, 8]
def baseStart_267582 : Nat := 118140960795 + 267582 * 2 ^ 59
def prefixEnd_267582 : Nat := 4983230072969 + 3 ^ 40 * 267582 * 2
def baseEnd_267582 : Nat := 27140381331649840571737

theorem tailTrace_267582 : CollatzResearch.WordTrace tailWord_267582 prefixEnd_267582 27140381331649840571737 := by
  unfold tailWord_267582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1219939664575448526549625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6506344877735725474931333 1219939664575448526549625)
  ·
    refine ⟨914954748431586394912219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1219939664575448526549625 914954748431586394912219)
    ·
      refine ⟨1372432122647379592368329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 914954748431586394912219 1372432122647379592368329)
      ·
        refine ⟨1029324091985534694276247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1372432122647379592368329 1029324091985534694276247)
        ·
          refine ⟨1543986137978302041414371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029324091985534694276247 1543986137978302041414371)
          ·
            refine ⟨2315979206967453062121557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1543986137978302041414371 2315979206967453062121557)
            ·
              refine ⟨27140381331649840571737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2315979206967453062121557 27140381331649840571737)
              ·
                rfl

theorem cell19_267582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 8].length) (baseStart_267582 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267582 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267582 prefixEnd_267582 := by exact prefixLift 267582
  have htrace : WordTrace (prefixWord ++ tailWord_267582) baseStart_267582 baseEnd_267582 := by
    simpa [prefixWord, tailWord_267582, baseEnd_267582] using wordTrace_append hprefix tailTrace_267582
  have hstable : (prefixWord ++ tailWord_267582).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267582).length < 2 ^ (prefixWord ++ tailWord_267582).sum := by decide
  have hdescent : baseEnd_267582 < baseStart_267582 := by decide
  rcases family_descends (prefixWord ++ tailWord_267582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267584 : List Nat := [2, 1, 1, 2, 2, 1, 10]
def baseStart_267584 : Nat := 118140960795 + 267584 * 2 ^ 59
def prefixEnd_267584 : Nat := 4983230072969 + 3 ^ 40 * 267584 * 2
def baseEnd_267584 : Nat := 27140584188204703223587

theorem tailTrace_267584 : CollatzResearch.WordTrace tailWord_267584 prefixEnd_267584 27140584188204703223587 := by
  unfold tailWord_267584
  simp only [CollatzResearch.WordTrace]
  refine ⟨4879795131298171276984903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6506393508397561702646537 4879795131298171276984903)
  ·
    refine ⟨7319692696947256915477355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4879795131298171276984903 7319692696947256915477355)
    ·
      refine ⟨10979539045420885373216033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7319692696947256915477355 10979539045420885373216033)
      ·
        refine ⟨8234654284065664029912025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10979539045420885373216033 8234654284065664029912025)
        ·
          refine ⟨6175990713049248022434019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8234654284065664029912025 6175990713049248022434019)
          ·
            refine ⟨9263986069573872033651029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6175990713049248022434019 9263986069573872033651029)
            ·
              refine ⟨27140584188204703223587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9263986069573872033651029 27140584188204703223587)
              ·
                rfl

theorem cell19_267584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 10].length) (baseStart_267584 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267584 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267584 prefixEnd_267584 := by exact prefixLift 267584
  have htrace : WordTrace (prefixWord ++ tailWord_267584) baseStart_267584 baseEnd_267584 := by
    simpa [prefixWord, tailWord_267584, baseEnd_267584] using wordTrace_append hprefix tailTrace_267584
  have hstable : (prefixWord ++ tailWord_267584).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267584).length < 2 ^ (prefixWord ++ tailWord_267584).sum := by decide
  have hdescent : baseEnd_267584 < baseStart_267584 := by decide
  rcases family_descends (prefixWord ++ tailWord_267584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267603 : List Nat := [1, 1, 1, 2, 1, 1, 6, 6]
def baseStart_267603 : Nat := 118140960795 + 267603 * 2 ^ 59
def prefixEnd_267603 : Nat := 4983230072969 + 3 ^ 40 * 267603 * 2
def baseEnd_267603 : Nat := 81427533976427695248487

theorem tailTrace_267603 : CollatzResearch.WordTrace tailWord_267603 prefixEnd_267603 81427533976427695248487 := by
  unfold tailWord_267603
  simp only [CollatzResearch.WordTrace]
  refine ⟨9760283249527508798911463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6506855499685005865940975 9760283249527508798911463)
  ·
    refine ⟨14640424874291263198367195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9760283249527508798911463 14640424874291263198367195)
    ·
      refine ⟨21960637311436894797550793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14640424874291263198367195 21960637311436894797550793)
      ·
        refine ⟨16470477983577671098163095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21960637311436894797550793 16470477983577671098163095)
        ·
          refine ⟨24705716975366506647244643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16470477983577671098163095 24705716975366506647244643)
          ·
            refine ⟨37058575463049759970866965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24705716975366506647244643 37058575463049759970866965)
            ·
              refine ⟨1737120724830457498634389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37058575463049759970866965 1737120724830457498634389)
              ·
                refine ⟨81427533976427695248487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1737120724830457498634389 81427533976427695248487)
                ·
                  rfl

theorem cell19_267603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_267603 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267603 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267603 prefixEnd_267603 := by exact prefixLift 267603
  have htrace : WordTrace (prefixWord ++ tailWord_267603) baseStart_267603 baseEnd_267603 := by
    simpa [prefixWord, tailWord_267603, baseEnd_267603] using wordTrace_append hprefix tailTrace_267603
  have hstable : (prefixWord ++ tailWord_267603).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267603).length < 2 ^ (prefixWord ++ tailWord_267603).sum := by decide
  have hdescent : baseEnd_267603 < baseStart_267603 := by decide
  rcases family_descends (prefixWord ++ tailWord_267603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267620 : List Nat := [2, 3, 1, 1, 3, 3, 1, 5]
def baseStart_267620 : Nat := 118140960795 + 267620 * 2 ^ 59
def prefixEnd_267620 : Nat := 4983230072969 + 3 ^ 40 * 267620 * 2
def baseEnd_267620 : Nat := 81432706818576692870663

theorem tailTrace_267620 : CollatzResearch.WordTrace tailWord_267620 prefixEnd_267620 81432706818576692870663 := by
  unfold tailWord_267620
  simp only [CollatzResearch.WordTrace]
  refine ⟨4880451645232960351140157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6507268860310613801520209 4880451645232960351140157)
  ·
    refine ⟨1830169366962360131677559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4880451645232960351140157 1830169366962360131677559)
    ·
      refine ⟨2745254050443540197516339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1830169366962360131677559 2745254050443540197516339)
      ·
        refine ⟨4117881075665310296274509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2745254050443540197516339 4117881075665310296274509)
        ·
          refine ⟨1544205403374491361102941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4117881075665310296274509 1544205403374491361102941)
          ·
            refine ⟨579077026265434260413603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1544205403374491361102941 579077026265434260413603)
            ·
              refine ⟨868615539398151390620405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579077026265434260413603 868615539398151390620405)
              ·
                refine ⟨81432706818576692870663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 868615539398151390620405 81432706818576692870663)
                ·
                  rfl

theorem cell19_267620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_267620 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267620 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267620 prefixEnd_267620 := by exact prefixLift 267620
  have htrace : WordTrace (prefixWord ++ tailWord_267620) baseStart_267620 baseEnd_267620 := by
    simpa [prefixWord, tailWord_267620, baseEnd_267620] using wordTrace_append hprefix tailTrace_267620
  have hstable : (prefixWord ++ tailWord_267620).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267620).length < 2 ^ (prefixWord ++ tailWord_267620).sum := by decide
  have hdescent : baseEnd_267620 < baseStart_267620 := by decide
  rcases family_descends (prefixWord ++ tailWord_267620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267637 : List Nat := [1, 3, 4, 1, 3, 2, 5]
def baseStart_267637 : Nat := 118140960795 + 267637 * 2 ^ 59
def prefixEnd_267637 : Nat := 4983230072969 + 3 ^ 40 * 267637 * 2
def baseEnd_267637 : Nat := 27145959886908563497613

theorem tailTrace_267637 : CollatzResearch.WordTrace tailWord_267637 prefixEnd_267637 27145959886908563497613 := by
  unfold tailWord_267637
  simp only [CollatzResearch.WordTrace]
  refine ⟨9761523331404332605649165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6507682220936221737099443 9761523331404332605649165)
  ·
    refine ⟨3660571249276624727118437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9761523331404332605649165 3660571249276624727118437)
    ·
      refine ⟨686357109239367136334707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3660571249276624727118437 686357109239367136334707)
      ·
        refine ⟨1029535663859050704502061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686357109239367136334707 1029535663859050704502061)
        ·
          refine ⟨386075873947144014188273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1029535663859050704502061 386075873947144014188273)
          ·
            refine ⟨289556905460358010641205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386075873947144014188273 289556905460358010641205)
            ·
              refine ⟨27145959886908563497613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 289556905460358010641205 27145959886908563497613)
              ·
                rfl

theorem cell19_267637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 5].length) (baseStart_267637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267637 prefixEnd_267637 := by exact prefixLift 267637
  have htrace : WordTrace (prefixWord ++ tailWord_267637) baseStart_267637 baseEnd_267637 := by
    simpa [prefixWord, tailWord_267637, baseEnd_267637] using wordTrace_append hprefix tailTrace_267637
  have hstable : (prefixWord ++ tailWord_267637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267637).length < 2 ^ (prefixWord ++ tailWord_267637).sum := by decide
  have hdescent : baseEnd_267637 < baseStart_267637 := by decide
  rcases family_descends (prefixWord ++ tailWord_267637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267641 : List Nat := [1, 2, 1, 3, 2, 1, 9]
def baseStart_267641 : Nat := 118140960795 + 267641 * 2 ^ 59
def prefixEnd_267641 : Nat := 4983230072969 + 3 ^ 40 * 267641 * 2
def baseEnd_267641 : Nat := 27146365600018288801313

theorem tailTrace_267641 : CollatzResearch.WordTrace tailWord_267641 prefixEnd_267641 27146365600018288801313 := by
  unfold tailWord_267641
  simp only [CollatzResearch.WordTrace]
  refine ⟨9761669223389841288794777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6507779482259894192529851 9761669223389841288794777)
  ·
    refine ⟨7321251917542380966596083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9761669223389841288794777 7321251917542380966596083)
    ·
      refine ⟨10981877876313571449894125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7321251917542380966596083 10981877876313571449894125)
      ·
        refine ⟨4118204203617589293710297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10981877876313571449894125 4118204203617589293710297)
        ·
          refine ⟨3088653152713191970282723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4118204203617589293710297 3088653152713191970282723)
          ·
            refine ⟨4632979729069787955424085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3088653152713191970282723 4632979729069787955424085)
            ·
              refine ⟨27146365600018288801313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4632979729069787955424085 27146365600018288801313)
              ·
                rfl

theorem cell19_267641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 9].length) (baseStart_267641 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267641 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267641 prefixEnd_267641 := by exact prefixLift 267641
  have htrace : WordTrace (prefixWord ++ tailWord_267641) baseStart_267641 baseEnd_267641 := by
    simpa [prefixWord, tailWord_267641, baseEnd_267641] using wordTrace_append hprefix tailTrace_267641
  have hstable : (prefixWord ++ tailWord_267641).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267641).length < 2 ^ (prefixWord ++ tailWord_267641).sum := by decide
  have hdescent : baseEnd_267641 < baseStart_267641 := by decide
  rcases family_descends (prefixWord ++ tailWord_267641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267677 : List Nat := [1, 4, 2, 1, 3, 1, 2, 5]
def baseStart_267677 : Nat := 118140960795 + 267677 * 2 ^ 59
def prefixEnd_267677 : Nat := 4983230072969 + 3 ^ 40 * 267677 * 2
def baseEnd_267677 : Nat := 81450051054017449603841

theorem tailTrace_267677 : CollatzResearch.WordTrace tailWord_267677 prefixEnd_267677 81450051054017449603841 := by
  unfold tailWord_267677
  simp only [CollatzResearch.WordTrace]
  refine ⟨9762982251259419437105285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6508654834172946291403523 9762982251259419437105285)
  ·
    refine ⟨1830559172111141144457241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9762982251259419437105285 1830559172111141144457241)
    ·
      refine ⟨1372919379083355858342931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1830559172111141144457241 1372919379083355858342931)
      ·
        refine ⟨2059379068625033787514397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1372919379083355858342931 2059379068625033787514397)
        ·
          refine ⟨772267150734387670317899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2059379068625033787514397 772267150734387670317899)
          ·
            refine ⟨1158400726101581505476849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772267150734387670317899 1158400726101581505476849)
            ·
              refine ⟨868800544576186129107637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1158400726101581505476849 868800544576186129107637)
              ·
                refine ⟨81450051054017449603841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 868800544576186129107637 81450051054017449603841)
                ·
                  rfl

theorem cell19_267677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_267677 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267677 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267677 prefixEnd_267677 := by exact prefixLift 267677
  have htrace : WordTrace (prefixWord ++ tailWord_267677) baseStart_267677 baseEnd_267677 := by
    simpa [prefixWord, tailWord_267677, baseEnd_267677] using wordTrace_append hprefix tailTrace_267677
  have hstable : (prefixWord ++ tailWord_267677).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267677).length < 2 ^ (prefixWord ++ tailWord_267677).sum := by decide
  have hdescent : baseEnd_267677 < baseStart_267677 := by decide
  rcases family_descends (prefixWord ++ tailWord_267677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267736 : List Nat := [2, 1, 2, 2, 2, 1, 2, 7]
def baseStart_267736 : Nat := 118140960795 + 267736 * 2 ^ 59
def prefixEnd_267736 : Nat := 4983230072969 + 3 ^ 40 * 267736 * 2
def baseEnd_267736 : Nat := 81468003859122794292569

theorem tailTrace_267736 : CollatzResearch.WordTrace tailWord_267736 prefixEnd_267736 81468003859122794292569 := by
  unfold tailWord_267736
  simp only [CollatzResearch.WordTrace]
  refine ⟨4882567079022836256751531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6510089438697115009002041 4882567079022836256751531)
  ·
    refine ⟨7323850618534254385127297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4882567079022836256751531 7323850618534254385127297)
    ·
      refine ⟨5492887963900690788845473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7323850618534254385127297 5492887963900690788845473)
      ·
        refine ⟨4119665972925518091634105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5492887963900690788845473 4119665972925518091634105)
        ·
          refine ⟨3089749479694138568725579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4119665972925518091634105 3089749479694138568725579)
          ·
            refine ⟨4634624219541207853088369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3089749479694138568725579 4634624219541207853088369)
            ·
              refine ⟨3475968164655905889816277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4634624219541207853088369 3475968164655905889816277)
              ·
                refine ⟨81468003859122794292569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3475968164655905889816277 81468003859122794292569)
                ·
                  rfl

theorem cell19_267736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_267736 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267736 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267736 prefixEnd_267736 := by exact prefixLift 267736
  have htrace : WordTrace (prefixWord ++ tailWord_267736) baseStart_267736 baseEnd_267736 := by
    simpa [prefixWord, tailWord_267736, baseEnd_267736] using wordTrace_append hprefix tailTrace_267736
  have hstable : (prefixWord ++ tailWord_267736).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267736).length < 2 ^ (prefixWord ++ tailWord_267736).sum := by decide
  have hdescent : baseEnd_267736 < baseStart_267736 := by decide
  rcases family_descends (prefixWord ++ tailWord_267736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267787 : List Nat := [1, 1, 1, 1, 9, 1, 2, 3]
def baseStart_267787 : Nat := 118140960795 + 267787 * 2 ^ 59
def prefixEnd_267787 : Nat := 4983230072969 + 3 ^ 40 * 267787 * 2
def baseEnd_267787 : Nat := 81483522385569787159097

theorem tailTrace_267787 : CollatzResearch.WordTrace tailWord_267787 prefixEnd_267787 81483522385569787159097 := by
  unfold tailWord_267787
  simp only [CollatzResearch.WordTrace]
  refine ⟨9766994280860908223609615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6511329520573938815739743 9766994280860908223609615)
  ·
    refine ⟨14650491421291362335414423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9766994280860908223609615 14650491421291362335414423)
    ·
      refine ⟨21975737131937043503121635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14650491421291362335414423 21975737131937043503121635)
      ·
        refine ⟨32963605697905565254682453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21975737131937043503121635 32963605697905565254682453)
        ·
          refine ⟨193146127136165421414155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 32963605697905565254682453 193146127136165421414155)
          ·
            refine ⟨289719190704248132121233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193146127136165421414155 289719190704248132121233)
            ·
              refine ⟨217289393028186099090925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289719190704248132121233 217289393028186099090925)
              ·
                refine ⟨81483522385569787159097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217289393028186099090925 81483522385569787159097)
                ·
                  rfl

theorem cell19_267787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 3].length) (baseStart_267787 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267787 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267787 prefixEnd_267787 := by exact prefixLift 267787
  have htrace : WordTrace (prefixWord ++ tailWord_267787) baseStart_267787 baseEnd_267787 := by
    simpa [prefixWord, tailWord_267787, baseEnd_267787] using wordTrace_append hprefix tailTrace_267787
  have hstable : (prefixWord ++ tailWord_267787).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267787).length < 2 ^ (prefixWord ++ tailWord_267787).sum := by decide
  have hdescent : baseEnd_267787 < baseStart_267787 := by decide
  rcases family_descends (prefixWord ++ tailWord_267787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267793 : List Nat := [1, 2, 2, 1, 1, 2, 5, 5]
def baseStart_267793 : Nat := 118140960795 + 267793 * 2 ^ 59
def prefixEnd_267793 : Nat := 4983230072969 + 3 ^ 40 * 267793 * 2
def baseEnd_267793 : Nat := 81485348094563551025747

theorem tailTrace_267793 : CollatzResearch.WordTrace tailWord_267793 prefixEnd_267793 81485348094563551025747 := by
  unfold tailWord_267793
  simp only [CollatzResearch.WordTrace]
  refine ⟨9767213118839171248328033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6511475412559447498885355 9767213118839171248328033)
  ·
    refine ⟨7325409839129378436246025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9767213118839171248328033 7325409839129378436246025)
    ·
      refine ⟨5494057379347033827184519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7325409839129378436246025 5494057379347033827184519)
      ·
        refine ⟨8241086069020550740776779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5494057379347033827184519 8241086069020550740776779)
        ·
          refine ⟨12361629103530826111165169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8241086069020550740776779 12361629103530826111165169)
          ·
            refine ⟨9271221827648119583373877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12361629103530826111165169 9271221827648119583373877)
            ·
              refine ⟨869177046342011210941301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9271221827648119583373877 869177046342011210941301)
              ·
                refine ⟨81485348094563551025747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 869177046342011210941301 81485348094563551025747)
                ·
                  rfl

theorem cell19_267793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_267793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267793 prefixEnd_267793 := by exact prefixLift 267793
  have htrace : WordTrace (prefixWord ++ tailWord_267793) baseStart_267793 baseEnd_267793 := by
    simpa [prefixWord, tailWord_267793, baseEnd_267793] using wordTrace_append hprefix tailTrace_267793
  have hstable : (prefixWord ++ tailWord_267793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267793).length < 2 ^ (prefixWord ++ tailWord_267793).sum := by decide
  have hdescent : baseEnd_267793 < baseStart_267793 := by decide
  rcases family_descends (prefixWord ++ tailWord_267793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267829 : List Nat := [1, 3, 3, 1, 1, 4, 2, 4]
def baseStart_267829 : Nat := 118140960795 + 267829 * 2 ^ 59
def prefixEnd_267829 : Nat := 4983230072969 + 3 ^ 40 * 267829 * 2
def baseEnd_267829 : Nat := 81496302348526134225649

theorem tailTrace_267829 : CollatzResearch.WordTrace tailWord_267829 prefixEnd_267829 81496302348526134225649 := by
  unfold tailWord_267829
  simp only [CollatzResearch.WordTrace]
  refine ⟨9768526146708749396638541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6512350764472499597759027 9768526146708749396638541)
  ·
    refine ⟨3663197305015781023739453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9768526146708749396638541 3663197305015781023739453)
    ·
      refine ⟨1373698989380917883902295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3663197305015781023739453 1373698989380917883902295)
      ·
        refine ⟨2060548484071376825853443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1373698989380917883902295 2060548484071376825853443)
        ·
          refine ⟨3090822726107065238780165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2060548484071376825853443 3090822726107065238780165)
          ·
            refine ⟨579529261145074732271281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3090822726107065238780165 579529261145074732271281)
            ·
              refine ⟨434646945858806049203461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579529261145074732271281 434646945858806049203461)
              ·
                refine ⟨81496302348526134225649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 434646945858806049203461 81496302348526134225649)
                ·
                  rfl

theorem cell19_267829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_267829 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267829 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267829 prefixEnd_267829 := by exact prefixLift 267829
  have htrace : WordTrace (prefixWord ++ tailWord_267829) baseStart_267829 baseEnd_267829 := by
    simpa [prefixWord, tailWord_267829, baseEnd_267829] using wordTrace_append hprefix tailTrace_267829
  have hstable : (prefixWord ++ tailWord_267829).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267829).length < 2 ^ (prefixWord ++ tailWord_267829).sum := by decide
  have hdescent : baseEnd_267829 < baseStart_267829 := by decide
  rcases family_descends (prefixWord ++ tailWord_267829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267831 : List Nat := [1, 1, 3, 1, 2, 4, 1, 6]
def baseStart_267831 : Nat := 118140960795 + 267831 * 2 ^ 59
def prefixEnd_267831 : Nat := 4983230072969 + 3 ^ 40 * 267831 * 2
def baseEnd_267831 : Nat := 81496910918190722181199

theorem tailTrace_267831 : CollatzResearch.WordTrace tailWord_267831 prefixEnd_267831 81496910918190722181199 := by
  unfold tailWord_267831
  simp only [CollatzResearch.WordTrace]
  refine ⟨9768599092701503738211347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6512399395134335825474231 9768599092701503738211347)
  ·
    refine ⟨14652898639052255607317021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9768599092701503738211347 14652898639052255607317021)
    ·
      refine ⟨5494836989644595852743883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14652898639052255607317021 5494836989644595852743883)
      ·
        refine ⟨8242255484466893779115825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5494836989644595852743883 8242255484466893779115825)
        ·
          refine ⟨6181691613350170334336869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8242255484466893779115825 6181691613350170334336869)
          ·
            refine ⟨1159067177503156937688163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6181691613350170334336869 1159067177503156937688163)
            ·
              refine ⟨1738600766254735406532245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159067177503156937688163 1738600766254735406532245)
              ·
                refine ⟨81496910918190722181199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1738600766254735406532245 81496910918190722181199)
                ·
                  rfl

theorem cell19_267831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_267831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267831 prefixEnd_267831 := by exact prefixLift 267831
  have htrace : WordTrace (prefixWord ++ tailWord_267831) baseStart_267831 baseEnd_267831 := by
    simpa [prefixWord, tailWord_267831, baseEnd_267831] using wordTrace_append hprefix tailTrace_267831
  have hstable : (prefixWord ++ tailWord_267831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267831).length < 2 ^ (prefixWord ++ tailWord_267831).sum := by decide
  have hdescent : baseEnd_267831 < baseStart_267831 := by decide
  rcases family_descends (prefixWord ++ tailWord_267831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267850 : List Nat := [3, 1, 2, 1, 1, 3, 1, 7]
def baseStart_267850 : Nat := 118140960795 + 267850 * 2 ^ 59
def prefixEnd_267850 : Nat := 4983230072969 + 3 ^ 40 * 267850 * 2
def baseEnd_267850 : Nat := 81502692330004307758925

theorem tailTrace_267850 : CollatzResearch.WordTrace tailWord_267850 prefixEnd_267850 81502692330004307758925 := by
  unfold tailWord_267850
  simp only [CollatzResearch.WordTrace]
  refine ⟨2442323019908167495788251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6512861386421779988768669 2442323019908167495788251)
  ·
    refine ⟨3663484529862251243682377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2442323019908167495788251 3663484529862251243682377)
    ·
      refine ⟨2747613397396688432761783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3663484529862251243682377 2747613397396688432761783)
      ·
        refine ⟨4121420096095032649142675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2747613397396688432761783 4121420096095032649142675)
        ·
          refine ⟨6182130144142548973714013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4121420096095032649142675 6182130144142548973714013)
          ·
            refine ⟨2318298804053455865142755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6182130144142548973714013 2318298804053455865142755)
            ·
              refine ⟨3477448206080183797714133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2318298804053455865142755 3477448206080183797714133)
              ·
                refine ⟨81502692330004307758925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3477448206080183797714133 81502692330004307758925)
                ·
                  rfl

theorem cell19_267850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_267850 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267850 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267850 prefixEnd_267850 := by exact prefixLift 267850
  have htrace : WordTrace (prefixWord ++ tailWord_267850) baseStart_267850 baseEnd_267850 := by
    simpa [prefixWord, tailWord_267850, baseEnd_267850] using wordTrace_append hprefix tailTrace_267850
  have hstable : (prefixWord ++ tailWord_267850).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267850).length < 2 ^ (prefixWord ++ tailWord_267850).sum := by decide
  have hdescent : baseEnd_267850 < baseStart_267850 := by decide
  rcases family_descends (prefixWord ++ tailWord_267850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267958 : List Nat := [5, 1, 3, 1, 1, 1, 4, 3]
def baseStart_267958 : Nat := 118140960795 + 267958 * 2 ^ 59
def prefixEnd_267958 : Nat := 4983230072969 + 3 ^ 40 * 267958 * 2
def baseEnd_267958 : Nat := 81535555091892057358631

theorem tailTrace_267958 : CollatzResearch.WordTrace tailWord_267958 prefixEnd_267958 81535555091892057358631 := by
  unfold tailWord_267958
  simp only [CollatzResearch.WordTrace]
  refine ⟨610826947702587776755283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6515487442160936285389685 610826947702587776755283)
  ·
    refine ⟨916240421553881665132925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 610826947702587776755283 916240421553881665132925)
    ·
      refine ⟨343590158082705624424847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 916240421553881665132925 343590158082705624424847)
      ·
        refine ⟨515385237124058436637271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343590158082705624424847 515385237124058436637271)
        ·
          refine ⟨773077855686087654955907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515385237124058436637271 773077855686087654955907)
          ·
            refine ⟨1159616783529131482433861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773077855686087654955907 1159616783529131482433861)
            ·
              refine ⟨217428146911712152956349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1159616783529131482433861 217428146911712152956349)
              ·
                refine ⟨81535555091892057358631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217428146911712152956349 81535555091892057358631)
                ·
                  rfl

theorem cell19_267958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_267958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267958 prefixEnd_267958 := by exact prefixLift 267958
  have htrace : WordTrace (prefixWord ++ tailWord_267958) baseStart_267958 baseEnd_267958 := by
    simpa [prefixWord, tailWord_267958, baseEnd_267958] using wordTrace_append hprefix tailTrace_267958
  have hstable : (prefixWord ++ tailWord_267958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267958).length < 2 ^ (prefixWord ++ tailWord_267958).sum := by decide
  have hdescent : baseEnd_267958 < baseStart_267958 := by decide
  rcases family_descends (prefixWord ++ tailWord_267958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267962 : List Nat := [3, 1, 1, 1, 2, 4, 4, 3]
def baseStart_267962 : Nat := 118140960795 + 267962 * 2 ^ 59
def prefixEnd_267962 : Nat := 4983230072969 + 3 ^ 40 * 267962 * 2
def baseEnd_267962 : Nat := 81536772231221233269731

theorem tailTrace_267962 : CollatzResearch.WordTrace tailWord_267962 prefixEnd_267962 81536772231221233269731 := by
  unfold tailWord_267962
  simp only [CollatzResearch.WordTrace]
  refine ⟨2443344263806728277807535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6515584703484608740820093 2443344263806728277807535)
  ·
    refine ⟨3665016395710092416711303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2443344263806728277807535 3665016395710092416711303)
    ·
      refine ⟨5497524593565138625066955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3665016395710092416711303 5497524593565138625066955)
      ·
        refine ⟨8246286890347707937600433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5497524593565138625066955 8246286890347707937600433)
        ·
          refine ⟨6184715167760780953200325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8246286890347707937600433 6184715167760780953200325)
          ·
            refine ⟨1159634093955146428725061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6184715167760780953200325 1159634093955146428725061)
            ·
              refine ⟨217431392616589955385949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1159634093955146428725061 217431392616589955385949)
              ·
                refine ⟨81536772231221233269731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217431392616589955385949 81536772231221233269731)
                ·
                  rfl

theorem cell19_267962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_267962 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_267962 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_267962 prefixEnd_267962 := by exact prefixLift 267962
  have htrace : WordTrace (prefixWord ++ tailWord_267962) baseStart_267962 baseEnd_267962 := by
    simpa [prefixWord, tailWord_267962, baseEnd_267962] using wordTrace_append hprefix tailTrace_267962
  have hstable : (prefixWord ++ tailWord_267962).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267962).length < 2 ^ (prefixWord ++ tailWord_267962).sum := by decide
  have hdescent : baseEnd_267962 < baseStart_267962 := by decide
  rcases family_descends (prefixWord ++ tailWord_267962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268076 : List Nat := [2, 2, 1, 1, 1, 6, 3, 3]
def baseStart_268076 : Nat := 118140960795 + 268076 * 2 ^ 59
def prefixEnd_268076 : Nat := 4983230072969 + 3 ^ 40 * 268076 * 2
def baseEnd_268076 : Nat := 81571460702102746736087

theorem tailTrace_268076 : CollatzResearch.WordTrace tailWord_268076 prefixEnd_268076 81571460702102746736087 := by
  unfold tailWord_268076
  simp only [CollatzResearch.WordTrace]
  refine ⟨4888767488406955290440041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6518356651209273720586721 4888767488406955290440041)
  ·
    refine ⟨3666575616305216467830031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4888767488406955290440041 3666575616305216467830031)
    ·
      refine ⟨5499863424457824701745047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3666575616305216467830031 5499863424457824701745047)
      ·
        refine ⟨8249795136686737052617571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5499863424457824701745047 8249795136686737052617571)
        ·
          refine ⟨12374692705030105578926357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8249795136686737052617571 12374692705030105578926357)
          ·
            refine ⟨580063720548286199012173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12374692705030105578926357 580063720548286199012173)
            ·
              refine ⟨217523895205607324629565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 580063720548286199012173 217523895205607324629565)
              ·
                refine ⟨81571460702102746736087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217523895205607324629565 81571460702102746736087)
                ·
                  rfl

theorem cell19_268076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_268076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268076 prefixEnd_268076 := by exact prefixLift 268076
  have htrace : WordTrace (prefixWord ++ tailWord_268076) baseStart_268076 baseEnd_268076 := by
    simpa [prefixWord, tailWord_268076, baseEnd_268076] using wordTrace_append hprefix tailTrace_268076
  have hstable : (prefixWord ++ tailWord_268076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268076).length < 2 ^ (prefixWord ++ tailWord_268076).sum := by decide
  have hdescent : baseEnd_268076 < baseStart_268076 := by decide
  rcases family_descends (prefixWord ++ tailWord_268076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268131 : List Nat := [1, 1, 1, 5, 4, 2, 2, 3]
def baseStart_268131 : Nat := 118140960795 + 268131 * 2 ^ 59
def prefixEnd_268131 : Nat := 4983230072969 + 3 ^ 40 * 268131 * 2
def baseEnd_268131 : Nat := 81588196367878915513715

theorem tailTrace_268131 : CollatzResearch.WordTrace tailWord_268131 prefixEnd_268131 81588196367878915513715 := by
  unfold tailWord_268131
  simp only [CollatzResearch.WordTrace]
  refine ⟨9779540991614654974132247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6519693994409769982754831 9779540991614654974132247)
  ·
    refine ⟨14669311487421982461198371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9779540991614654974132247 14669311487421982461198371)
    ·
      refine ⟨22003967231132973691797557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14669311487421982461198371 22003967231132973691797557)
      ·
        refine ⟨2062871927918716283606021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22003967231132973691797557 2062871927918716283606021)
        ·
          refine ⟨386788486484759303176129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2062871927918716283606021 386788486484759303176129)
          ·
            refine ⟨290091364863569477382097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386788486484759303176129 290091364863569477382097)
            ·
              refine ⟨217568523647677108036573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290091364863569477382097 217568523647677108036573)
              ·
                refine ⟨81588196367878915513715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217568523647677108036573 81588196367878915513715)
                ·
                  rfl

theorem cell19_268131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 3].length) (baseStart_268131 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268131 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268131 prefixEnd_268131 := by exact prefixLift 268131
  have htrace : WordTrace (prefixWord ++ tailWord_268131) baseStart_268131 baseEnd_268131 := by
    simpa [prefixWord, tailWord_268131, baseEnd_268131] using wordTrace_append hprefix tailTrace_268131
  have hstable : (prefixWord ++ tailWord_268131).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268131).length < 2 ^ (prefixWord ++ tailWord_268131).sum := by decide
  have hdescent : baseEnd_268131 < baseStart_268131 := by decide
  rcases family_descends (prefixWord ++ tailWord_268131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268135 : List Nat := [1, 1, 5, 1, 2, 1, 3, 5]
def baseStart_268135 : Nat := 118140960795 + 268135 * 2 ^ 59
def prefixEnd_268135 : Nat := 4983230072969 + 3 ^ 40 * 268135 * 2
def baseEnd_268135 : Nat := 81589413507208091424815

theorem tailTrace_268135 : CollatzResearch.WordTrace tailWord_268135 prefixEnd_268135 81589413507208091424815 := by
  unfold tailWord_268135
  simp only [CollatzResearch.WordTrace]
  refine ⟨9779686883600163657277859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6519791255733442438185239 9779686883600163657277859)
  ·
    refine ⟨14669530325400245485916789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9779686883600163657277859 14669530325400245485916789)
    ·
      refine ⟨1375268468006273014304699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14669530325400245485916789 1375268468006273014304699)
      ·
        refine ⟨2062902702009409521457049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1375268468006273014304699 2062902702009409521457049)
        ·
          refine ⟨1547177026507057141092787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2062902702009409521457049 1547177026507057141092787)
          ·
            refine ⟨2320765539760585711639181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1547177026507057141092787 2320765539760585711639181)
            ·
              refine ⟨870287077410219641864693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2320765539760585711639181 870287077410219641864693)
              ·
                refine ⟨81589413507208091424815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 870287077410219641864693 81589413507208091424815)
                ·
                  rfl

theorem cell19_268135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_268135 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268135 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268135 prefixEnd_268135 := by exact prefixLift 268135
  have htrace : WordTrace (prefixWord ++ tailWord_268135) baseStart_268135 baseEnd_268135 := by
    simpa [prefixWord, tailWord_268135, baseEnd_268135] using wordTrace_append hprefix tailTrace_268135
  have hstable : (prefixWord ++ tailWord_268135).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268135).length < 2 ^ (prefixWord ++ tailWord_268135).sum := by decide
  have hdescent : baseEnd_268135 < baseStart_268135 := by decide
  rcases family_descends (prefixWord ++ tailWord_268135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268150 : List Nat := [5, 1, 1, 3, 2, 2, 5]
def baseStart_268150 : Nat := 118140960795 + 268150 * 2 ^ 59
def prefixEnd_268150 : Nat := 4983230072969 + 3 ^ 40 * 268150 * 2
def baseEnd_268150 : Nat := 27197992593230833697147

theorem tailTrace_268150 : CollatzResearch.WordTrace tailWord_268150 prefixEnd_268150 27197992593230833697147 := by
  unfold tailWord_268150
  simp only [CollatzResearch.WordTrace]
  refine ⟨611264623659113826192119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6520155985697214146049269 611264623659113826192119)
  ·
    refine ⟨916896935488670739288179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 611264623659113826192119 916896935488670739288179)
    ·
      refine ⟨1375345403233006108932269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 916896935488670739288179 1375345403233006108932269)
      ·
        refine ⟨515754526212377290849601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1375345403233006108932269 515754526212377290849601)
        ·
          refine ⟨386815894659282968137201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515754526212377290849601 386815894659282968137201)
          ·
            refine ⟨290111920994462226102901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386815894659282968137201 290111920994462226102901)
            ·
              refine ⟨27197992593230833697147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 290111920994462226102901 27197992593230833697147)
              ·
                rfl

theorem cell19_268150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 5].length) (baseStart_268150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268150 prefixEnd_268150 := by exact prefixLift 268150
  have htrace : WordTrace (prefixWord ++ tailWord_268150) baseStart_268150 baseEnd_268150 := by
    simpa [prefixWord, tailWord_268150, baseEnd_268150] using wordTrace_append hprefix tailTrace_268150
  have hstable : (prefixWord ++ tailWord_268150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268150).length < 2 ^ (prefixWord ++ tailWord_268150).sum := by decide
  have hdescent : baseEnd_268150 < baseStart_268150 := by decide
  rcases family_descends (prefixWord ++ tailWord_268150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268294 : List Nat := [6, 2, 1, 2, 2, 1, 2, 3]
def baseStart_268294 : Nat := 118140960795 + 268294 * 2 ^ 59
def prefixEnd_268294 : Nat := 4983230072969 + 3 ^ 40 * 268294 * 2
def baseEnd_268294 : Nat := 81637794795542833891049

theorem tailTrace_268294 : CollatzResearch.WordTrace tailWord_268294 prefixEnd_268294 81637794795542833891049 := by
  unfold tailWord_268294
  simp only [CollatzResearch.WordTrace]
  refine ⟨305796440313254181634873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6523657393349422541543957 305796440313254181634873)
  ·
    refine ⟨229347330234940636226155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305796440313254181634873 229347330234940636226155)
    ·
      refine ⟨344020995352410954339233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229347330234940636226155 344020995352410954339233)
      ·
        refine ⟨258015746514308215754425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344020995352410954339233 258015746514308215754425)
        ·
          refine ⟨193511809885731161815819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258015746514308215754425 193511809885731161815819)
          ·
            refine ⟨290267714828596742723729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193511809885731161815819 290267714828596742723729)
            ·
              refine ⟨217700786121447557042797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290267714828596742723729 217700786121447557042797)
              ·
                refine ⟨81637794795542833891049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217700786121447557042797 81637794795542833891049)
                ·
                  rfl

theorem cell19_268294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_268294 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268294 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268294 prefixEnd_268294 := by exact prefixLift 268294
  have htrace : WordTrace (prefixWord ++ tailWord_268294) baseStart_268294 baseEnd_268294 := by
    simpa [prefixWord, tailWord_268294, baseEnd_268294] using wordTrace_append hprefix tailTrace_268294
  have hstable : (prefixWord ++ tailWord_268294).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268294).length < 2 ^ (prefixWord ++ tailWord_268294).sum := by decide
  have hdescent : baseEnd_268294 < baseStart_268294 := by decide
  rcases family_descends (prefixWord ++ tailWord_268294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268325 : List Nat := [1, 3, 1, 2, 2, 5, 5]
def baseStart_268325 : Nat := 118140960795 + 268325 * 2 ^ 59
def prefixEnd_268325 : Nat := 4983230072969 + 3 ^ 40 * 268325 * 2
def baseEnd_268325 : Nat := 27215742541781315734025

theorem tailTrace_268325 : CollatzResearch.WordTrace tailWord_268325 prefixEnd_268325 27215742541781315734025 := by
  unfold tailWord_268325
  simp only [CollatzResearch.WordTrace]
  refine ⟨9786616752911826106694429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6524411168607884071129619 9786616752911826106694429)
  ·
    refine ⟨3669981282341934790010411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9786616752911826106694429 3669981282341934790010411)
    ·
      refine ⟨5504971923512902185015617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3669981282341934790010411 5504971923512902185015617)
      ·
        refine ⟨4128728942634676638761713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5504971923512902185015617 4128728942634676638761713)
        ·
          refine ⟨3096546706976007479071285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4128728942634676638761713 3096546706976007479071285)
          ·
            refine ⟨290301253779000701162933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3096546706976007479071285 290301253779000701162933)
            ·
              refine ⟨27215742541781315734025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 290301253779000701162933 27215742541781315734025)
              ·
                rfl

theorem cell19_268325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 5].length) (baseStart_268325 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268325 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268325 prefixEnd_268325 := by exact prefixLift 268325
  have htrace : WordTrace (prefixWord ++ tailWord_268325) baseStart_268325 baseEnd_268325 := by
    simpa [prefixWord, tailWord_268325, baseEnd_268325] using wordTrace_append hprefix tailTrace_268325
  have hstable : (prefixWord ++ tailWord_268325).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268325).length < 2 ^ (prefixWord ++ tailWord_268325).sum := by decide
  have hdescent : baseEnd_268325 < baseStart_268325 := by decide
  rcases family_descends (prefixWord ++ tailWord_268325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268340 : List Nat := [2, 5, 1, 2, 2, 1, 2, 4]
def baseStart_268340 : Nat := 118140960795 + 268340 * 2 ^ 59
def prefixEnd_268340 : Nat := 4983230072969 + 3 ^ 40 * 268340 * 2
def baseEnd_268340 : Nat := 81651791897828356868701

theorem tailTrace_268340 : CollatzResearch.WordTrace tailWord_268340 prefixEnd_268340 81651791897828356868701 := by
  unfold tailWord_268340
  simp only [CollatzResearch.WordTrace]
  refine ⟨4893581923928741834245237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6524775898571655778993649 4893581923928741834245237)
  ·
    refine ⟨458773305368319546960491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4893581923928741834245237 458773305368319546960491)
    ·
      refine ⟨688159958052479320440737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458773305368319546960491 688159958052479320440737)
      ·
        refine ⟨516119968539359490330553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 688159958052479320440737 516119968539359490330553)
        ·
          refine ⟨387089976404519617747915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516119968539359490330553 387089976404519617747915)
          ·
            refine ⟨580634964606779426621873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387089976404519617747915 580634964606779426621873)
            ·
              refine ⟨435476223455084569966405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 580634964606779426621873 435476223455084569966405)
              ·
                refine ⟨81651791897828356868701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 435476223455084569966405 81651791897828356868701)
                ·
                  rfl

theorem cell19_268340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_268340 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268340 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268340 prefixEnd_268340 := by exact prefixLift 268340
  have htrace : WordTrace (prefixWord ++ tailWord_268340) baseStart_268340 baseEnd_268340 := by
    simpa [prefixWord, tailWord_268340, baseEnd_268340] using wordTrace_append hprefix tailTrace_268340
  have hstable : (prefixWord ++ tailWord_268340).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268340).length < 2 ^ (prefixWord ++ tailWord_268340).sum := by decide
  have hdescent : baseEnd_268340 < baseStart_268340 := by decide
  rcases family_descends (prefixWord ++ tailWord_268340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268342 : List Nat := [5, 1, 2, 1, 1, 1, 4, 4]
def baseStart_268342 : Nat := 118140960795 + 268342 * 2 ^ 59
def prefixEnd_268342 : Nat := 4983230072969 + 3 ^ 40 * 268342 * 2
def baseEnd_268342 : Nat := 81652400467492944824251

theorem tailTrace_268342 : CollatzResearch.WordTrace tailWord_268342 prefixEnd_268342 81652400467492944824251 := by
  unfold tailWord_268342
  simp only [CollatzResearch.WordTrace]
  refine ⟨611702299615639875628955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6524824529233492006708853 611702299615639875628955)
  ·
    refine ⟨917553449423459813443433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 611702299615639875628955 917553449423459813443433)
    ·
      refine ⟨688165087067594860082575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 917553449423459813443433 688165087067594860082575)
      ·
        refine ⟨1032247630601392290123863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688165087067594860082575 1032247630601392290123863)
        ·
          refine ⟨1548371445902088435185795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1032247630601392290123863 1548371445902088435185795)
          ·
            refine ⟨2322557168853132652778693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1548371445902088435185795 2322557168853132652778693)
            ·
              refine ⟨435479469159962372396005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2322557168853132652778693 435479469159962372396005)
              ·
                refine ⟨81652400467492944824251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 435479469159962372396005 81652400467492944824251)
                ·
                  rfl

theorem cell19_268342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_268342 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268342 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268342 prefixEnd_268342 := by exact prefixLift 268342
  have htrace : WordTrace (prefixWord ++ tailWord_268342) baseStart_268342 baseEnd_268342 := by
    simpa [prefixWord, tailWord_268342, baseEnd_268342] using wordTrace_append hprefix tailTrace_268342
  have hstable : (prefixWord ++ tailWord_268342).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268342).length < 2 ^ (prefixWord ++ tailWord_268342).sum := by decide
  have hdescent : baseEnd_268342 < baseStart_268342 := by decide
  rcases family_descends (prefixWord ++ tailWord_268342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268384 : List Nat := [2, 1, 1, 3, 2, 10]
def baseStart_268384 : Nat := 118140960795 + 268384 * 2 ^ 59
def prefixEnd_268384 : Nat := 4983230072969 + 3 ^ 40 * 268384 * 2
def baseEnd_268384 : Nat := 9073908936716587987867

theorem tailTrace_268384 : CollatzResearch.WordTrace tailWord_268384 prefixEnd_268384 9073908936716587987867 := by
  unfold tailWord_268384
  simp only [CollatzResearch.WordTrace]
  refine ⟨4894384329849039591546103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6525845773132052788728137 4894384329849039591546103)
  ·
    refine ⟨7341576494773559387319155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4894384329849039591546103 7341576494773559387319155)
    ·
      refine ⟨11012364742160339080978733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7341576494773559387319155 11012364742160339080978733)
      ·
        refine ⟨4129636778310127155367025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11012364742160339080978733 4129636778310127155367025)
        ·
          refine ⟨3097227583732595366525269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4129636778310127155367025 3097227583732595366525269)
          ·
            refine ⟨9073908936716587987867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3097227583732595366525269 9073908936716587987867)
            ·
              rfl

theorem cell19_268384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 10].length) (baseStart_268384 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268384 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268384 prefixEnd_268384 := by exact prefixLift 268384
  have htrace : WordTrace (prefixWord ++ tailWord_268384) baseStart_268384 baseEnd_268384 := by
    simpa [prefixWord, tailWord_268384, baseEnd_268384] using wordTrace_append hprefix tailTrace_268384
  have hstable : (prefixWord ++ tailWord_268384).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268384).length < 2 ^ (prefixWord ++ tailWord_268384).sum := by decide
  have hdescent : baseEnd_268384 < baseStart_268384 := by decide
  rcases family_descends (prefixWord ++ tailWord_268384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268439 : List Nat := [1, 1, 3, 3, 4, 1, 6]
def baseStart_268439 : Nat := 118140960795 + 268439 * 2 ^ 59
def prefixEnd_268439 : Nat := 4983230072969 + 3 ^ 40 * 268439 * 2
def baseEnd_268439 : Nat := 27227305365408486889477

theorem tailTrace_268439 : CollatzResearch.WordTrace tailWord_268439 prefixEnd_268439 27227305365408486889477 := by
  unfold tailWord_268439
  simp only [CollatzResearch.WordTrace]
  refine ⟨9790774674498823576344371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6527183116332549050896247 9790774674498823576344371)
  ·
    refine ⟨14686162011748235364516557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9790774674498823576344371 14686162011748235364516557)
    ·
      refine ⟨5507310754405588261693709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14686162011748235364516557 5507310754405588261693709)
      ·
        refine ⟨2065241532902095598135141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5507310754405588261693709 2065241532902095598135141)
        ·
          refine ⟨387232787419142924650339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2065241532902095598135141 387232787419142924650339)
          ·
            refine ⟨580849181128714386975509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387232787419142924650339 580849181128714386975509)
            ·
              refine ⟨27227305365408486889477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 580849181128714386975509 27227305365408486889477)
              ·
                rfl

theorem cell19_268439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 6].length) (baseStart_268439 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268439 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268439 prefixEnd_268439 := by exact prefixLift 268439
  have htrace : WordTrace (prefixWord ++ tailWord_268439) baseStart_268439 baseEnd_268439 := by
    simpa [prefixWord, tailWord_268439, baseEnd_268439] using wordTrace_append hprefix tailTrace_268439
  have hstable : (prefixWord ++ tailWord_268439).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268439).length < 2 ^ (prefixWord ++ tailWord_268439).sum := by decide
  have hdescent : baseEnd_268439 < baseStart_268439 := by decide
  rcases family_descends (prefixWord ++ tailWord_268439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268492 : List Nat := [2, 2, 1, 6, 2, 1, 5]
def baseStart_268492 : Nat := 118140960795 + 268492 * 2 ^ 59
def prefixEnd_268492 : Nat := 4983230072969 + 3 ^ 40 * 268492 * 2
def baseEnd_268492 : Nat := 27232681064112347163503

theorem tailTrace_268492 : CollatzResearch.WordTrace tailWord_268492 prefixEnd_268492 27232681064112347163503 := by
  unfold tailWord_268492
  simp only [CollatzResearch.WordTrace]
  refine ⟨4896353871653406814011865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6528471828871209085349153 4896353871653406814011865)
  ·
    refine ⟨3672265403740055110508899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4896353871653406814011865 3672265403740055110508899)
    ·
      refine ⟨5508398105610082665763349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3672265403740055110508899 5508398105610082665763349)
      ·
        refine ⟨258206161200472624957657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5508398105610082665763349 258206161200472624957657)
        ·
          refine ⟨193654620900354468718243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258206161200472624957657 193654620900354468718243)
          ·
            refine ⟨290481931350531703077365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193654620900354468718243 290481931350531703077365)
            ·
              refine ⟨27232681064112347163503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 290481931350531703077365 27232681064112347163503)
              ·
                rfl

theorem cell19_268492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 5].length) (baseStart_268492 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268492 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268492 prefixEnd_268492 := by exact prefixLift 268492
  have htrace : WordTrace (prefixWord ++ tailWord_268492) baseStart_268492 baseEnd_268492 := by
    simpa [prefixWord, tailWord_268492, baseEnd_268492] using wordTrace_append hprefix tailTrace_268492
  have hstable : (prefixWord ++ tailWord_268492).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268492).length < 2 ^ (prefixWord ++ tailWord_268492).sum := by decide
  have hdescent : baseEnd_268492 < baseStart_268492 := by decide
  rcases family_descends (prefixWord ++ tailWord_268492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268534 : List Nat := [5, 1, 1, 1, 1, 1, 4, 5]
def baseStart_268534 : Nat := 118140960795 + 268534 * 2 ^ 59
def prefixEnd_268534 : Nat := 4983230072969 + 3 ^ 40 * 268534 * 2
def baseEnd_268534 : Nat := 81710823155293388557061

theorem tailTrace_268534 : CollatzResearch.WordTrace tailWord_268534 prefixEnd_268534 81710823155293388557061 := by
  unfold tailWord_268534
  simp only [CollatzResearch.WordTrace]
  refine ⟨612139975572165925065791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6529493072769769867368437 612139975572165925065791)
  ·
    refine ⟨918209963358248887598687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 612139975572165925065791 918209963358248887598687)
    ·
      refine ⟨1377314945037373331398031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 918209963358248887598687 1377314945037373331398031)
      ·
        refine ⟨2065972417556059997097047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1377314945037373331398031 2065972417556059997097047)
        ·
          refine ⟨3098958626334089995645571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2065972417556059997097047 3098958626334089995645571)
          ·
            refine ⟨4648437939501134993468357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3098958626334089995645571 4648437939501134993468357)
            ·
              refine ⟨871582113656462811275317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4648437939501134993468357 871582113656462811275317)
              ·
                refine ⟨81710823155293388557061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 871582113656462811275317 81710823155293388557061)
                ·
                  rfl

theorem cell19_268534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_268534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268534 prefixEnd_268534 := by exact prefixLift 268534
  have htrace : WordTrace (prefixWord ++ tailWord_268534) baseStart_268534 baseEnd_268534 := by
    simpa [prefixWord, tailWord_268534, baseEnd_268534] using wordTrace_append hprefix tailTrace_268534
  have hstable : (prefixWord ++ tailWord_268534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268534).length < 2 ^ (prefixWord ++ tailWord_268534).sum := by decide
  have hdescent : baseEnd_268534 < baseStart_268534 := by decide
  rcases family_descends (prefixWord ++ tailWord_268534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268551 : List Nat := [1, 1, 4, 5, 2, 6]
def baseStart_268551 : Nat := 118140960795 + 268551 * 2 ^ 59
def prefixEnd_268551 : Nat := 4983230072969 + 3 ^ 40 * 268551 * 2
def baseEnd_268551 : Nat := 9079555110826931797693

theorem tailTrace_268551 : CollatzResearch.WordTrace tailWord_268551 prefixEnd_268551 9079555110826931797693 := by
  unfold tailWord_268551
  simp only [CollatzResearch.WordTrace]
  refine ⟨9794859650093066704421507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6529906433395377802947671 9794859650093066704421507)
  ·
    refine ⟨14692289475139600056632261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9794859650093066704421507 14692289475139600056632261)
    ·
      refine ⟨2754804276588675010618549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14692289475139600056632261 2754804276588675010618549)
      ·
        refine ⟨258262900930188282245489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2754804276588675010618549 258262900930188282245489)
        ·
          refine ⟨193697175697641211684117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258262900930188282245489 193697175697641211684117)
          ·
            refine ⟨9079555110826931797693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 193697175697641211684117 9079555110826931797693)
            ·
              rfl

theorem cell19_268551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 6].length) (baseStart_268551 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268551 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268551 prefixEnd_268551 := by exact prefixLift 268551
  have htrace : WordTrace (prefixWord ++ tailWord_268551) baseStart_268551 baseEnd_268551 := by
    simpa [prefixWord, tailWord_268551, baseEnd_268551] using wordTrace_append hprefix tailTrace_268551
  have hstable : (prefixWord ++ tailWord_268551).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268551).length < 2 ^ (prefixWord ++ tailWord_268551).sum := by decide
  have hdescent : baseEnd_268551 < baseStart_268551 := by decide
  rcases family_descends (prefixWord ++ tailWord_268551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268570 : List Nat := [3, 1, 1, 3, 4, 2, 1, 4]
def baseStart_268570 : Nat := 118140960795 + 268570 * 2 ^ 59
def prefixEnd_268570 : Nat := 4983230072969 + 3 ^ 40 * 268570 * 2
def baseEnd_268570 : Nat := 81721777409255971756963

theorem tailTrace_268570 : CollatzResearch.WordTrace tailWord_268570 prefixEnd_268570 81721777409255971756963 := by
  unfold tailWord_268570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2448888159256058237340791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6530368424682821966242109 2448888159256058237340791)
  ·
    refine ⟨3673332238884087356011187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2448888159256058237340791 3673332238884087356011187)
    ·
      refine ⟨5509998358326131034016781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3673332238884087356011187 5509998358326131034016781)
      ·
        refine ⟨2066249384372299137756293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5509998358326131034016781 2066249384372299137756293)
        ·
          refine ⟨387421759569806088329305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2066249384372299137756293 387421759569806088329305)
          ·
            refine ⟨290566319677354566246979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387421759569806088329305 290566319677354566246979)
            ·
              refine ⟨435849479516031849370469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290566319677354566246979 435849479516031849370469)
              ·
                refine ⟨81721777409255971756963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 435849479516031849370469 81721777409255971756963)
                ·
                  rfl

theorem cell19_268570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_268570 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268570 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268570 prefixEnd_268570 := by exact prefixLift 268570
  have htrace : WordTrace (prefixWord ++ tailWord_268570) baseStart_268570 baseEnd_268570 := by
    simpa [prefixWord, tailWord_268570, baseEnd_268570] using wordTrace_append hprefix tailTrace_268570
  have hstable : (prefixWord ++ tailWord_268570).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268570).length < 2 ^ (prefixWord ++ tailWord_268570).sum := by decide
  have hdescent : baseEnd_268570 < baseStart_268570 := by decide
  rcases family_descends (prefixWord ++ tailWord_268570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268631 : List Nat := [1, 1, 3, 2, 3, 1, 2, 6]
def baseStart_268631 : Nat := 118140960795 + 268631 * 2 ^ 59
def prefixEnd_268631 : Nat := 4983230072969 + 3 ^ 40 * 268631 * 2
def baseEnd_268631 : Nat := 81740338784025904401241

theorem tailTrace_268631 : CollatzResearch.WordTrace tailWord_268631 prefixEnd_268631 81740338784025904401241 := by
  unfold tailWord_268631
  simp only [CollatzResearch.WordTrace]
  refine ⟨9797777489803240367333747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6531851659868826911555831 9797777489803240367333747)
  ·
    refine ⟨14696666234704860551000621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9797777489803240367333747 14696666234704860551000621)
    ·
      refine ⟨5511249838014322706625233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14696666234704860551000621 5511249838014322706625233)
      ·
        refine ⟨4133437378510742029968925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5511249838014322706625233 4133437378510742029968925)
        ·
          refine ⟨1550039016941528261238347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4133437378510742029968925 1550039016941528261238347)
          ·
            refine ⟨2325058525412292391857521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550039016941528261238347 2325058525412292391857521)
            ·
              refine ⟨1743793894059219293893141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2325058525412292391857521 1743793894059219293893141)
              ·
                refine ⟨81740338784025904401241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1743793894059219293893141 81740338784025904401241)
                ·
                  rfl

theorem cell19_268631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_268631 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268631 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268631 prefixEnd_268631 := by exact prefixLift 268631
  have htrace : WordTrace (prefixWord ++ tailWord_268631) baseStart_268631 baseEnd_268631 := by
    simpa [prefixWord, tailWord_268631, baseEnd_268631] using wordTrace_append hprefix tailTrace_268631
  have hstable : (prefixWord ++ tailWord_268631).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268631).length < 2 ^ (prefixWord ++ tailWord_268631).sum := by decide
  have hdescent : baseEnd_268631 < baseStart_268631 := by decide
  rcases family_descends (prefixWord ++ tailWord_268631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268638 : List Nat := [4, 4, 2, 1, 1, 2, 2, 3]
def baseStart_268638 : Nat := 118140960795 + 268638 * 2 ^ 59
def prefixEnd_268638 : Nat := 4983230072969 + 3 ^ 40 * 268638 * 2
def baseEnd_268638 : Nat := 81742468777851962245667

theorem tailTrace_268638 : CollatzResearch.WordTrace tailWord_268638 prefixEnd_268638 81742468777851962245667 := by
  unfold tailWord_268638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1224754100097235070354821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6532021867185253708559045 1224754100097235070354821)
  ·
    refine ⟨229641393768231575691529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1224754100097235070354821 229641393768231575691529)
    ·
      refine ⟨172231045326173681768647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229641393768231575691529 172231045326173681768647)
      ·
        refine ⟨258346567989260522652971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172231045326173681768647 258346567989260522652971)
        ·
          refine ⟨387519851983890783979457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258346567989260522652971 387519851983890783979457)
          ·
            refine ⟨290639888987918087984593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387519851983890783979457 290639888987918087984593)
            ·
              refine ⟨217979916740938565988445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290639888987918087984593 217979916740938565988445)
              ·
                refine ⟨81742468777851962245667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217979916740938565988445 81742468777851962245667)
                ·
                  rfl

theorem cell19_268638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_268638 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268638 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268638 prefixEnd_268638 := by exact prefixLift 268638
  have htrace : WordTrace (prefixWord ++ tailWord_268638) baseStart_268638 baseEnd_268638 := by
    simpa [prefixWord, tailWord_268638, baseEnd_268638] using wordTrace_append hprefix tailTrace_268638
  have hstable : (prefixWord ++ tailWord_268638).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268638).length < 2 ^ (prefixWord ++ tailWord_268638).sum := by decide
  have hdescent : baseEnd_268638 < baseStart_268638 := by decide
  rcases family_descends (prefixWord ++ tailWord_268638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268648 : List Nat := [2, 1, 4, 2, 2, 2, 1, 5]
def baseStart_268648 : Nat := 118140960795 + 268648 * 2 ^ 59
def prefixEnd_268648 : Nat := 4983230072969 + 3 ^ 40 * 268648 * 2
def baseEnd_268648 : Nat := 81745511626174902023417

theorem tailTrace_268648 : CollatzResearch.WordTrace tailWord_268648 prefixEnd_268648 81745511626174902023417 := by
  unfold tailWord_268648
  simp only [CollatzResearch.WordTrace]
  refine ⟨4899198765370826135351299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6532265020494434847135065 4899198765370826135351299)
  ·
    refine ⟨7348798148056239203026949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4899198765370826135351299 7348798148056239203026949)
    ·
      refine ⟨1377899652760544850567553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7348798148056239203026949 1377899652760544850567553)
      ·
        refine ⟨1033424739570408637925665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1377899652760544850567553 1033424739570408637925665)
        ·
          refine ⟨775068554677806478444249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1033424739570408637925665 775068554677806478444249)
          ·
            refine ⟨581301416008354858833187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 775068554677806478444249 581301416008354858833187)
            ·
              refine ⟨871952124012532288249781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581301416008354858833187 871952124012532288249781)
              ·
                refine ⟨81745511626174902023417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 871952124012532288249781 81745511626174902023417)
                ·
                  rfl

theorem cell19_268648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_268648 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268648 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268648 prefixEnd_268648 := by exact prefixLift 268648
  have htrace : WordTrace (prefixWord ++ tailWord_268648) baseStart_268648 baseEnd_268648 := by
    simpa [prefixWord, tailWord_268648, baseEnd_268648] using wordTrace_append hprefix tailTrace_268648
  have hstable : (prefixWord ++ tailWord_268648).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268648).length < 2 ^ (prefixWord ++ tailWord_268648).sum := by decide
  have hdescent : baseEnd_268648 < baseStart_268648 := by decide
  rcases family_descends (prefixWord ++ tailWord_268648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268669 : List Nat := [1, 4, 1, 1, 2, 3, 7]
def baseStart_268669 : Nat := 118140960795 + 268669 * 2 ^ 59
def prefixEnd_268669 : Nat := 4983230072969 + 3 ^ 40 * 268669 * 2
def baseEnd_268669 : Nat := 27250633869217691852231

theorem tailTrace_268669 : CollatzResearch.WordTrace tailWord_268669 prefixEnd_268669 27250633869217691852231 := by
  unfold tailWord_268669
  simp only [CollatzResearch.WordTrace]
  refine ⟨9799163463665572857217061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6532775642443715238144707 9799163463665572857217061)
  ·
    refine ⟨1837343149437294910728199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9799163463665572857217061 1837343149437294910728199)
    ·
      refine ⟨2756014724155942366092299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1837343149437294910728199 2756014724155942366092299)
      ·
        refine ⟨4134022086233913549138449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2756014724155942366092299 4134022086233913549138449)
        ·
          refine ⟨3100516564675435161853837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4134022086233913549138449 3100516564675435161853837)
          ·
            refine ⟨1162693711753288185695189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3100516564675435161853837 1162693711753288185695189)
            ·
              refine ⟨27250633869217691852231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1162693711753288185695189 27250633869217691852231)
              ·
                rfl

theorem cell19_268669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 7].length) (baseStart_268669 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268669 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268669 prefixEnd_268669 := by exact prefixLift 268669
  have htrace : WordTrace (prefixWord ++ tailWord_268669) baseStart_268669 baseEnd_268669 := by
    simpa [prefixWord, tailWord_268669, baseEnd_268669] using wordTrace_append hprefix tailTrace_268669
  have hstable : (prefixWord ++ tailWord_268669).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268669).length < 2 ^ (prefixWord ++ tailWord_268669).sum := by decide
  have hdescent : baseEnd_268669 < baseStart_268669 := by decide
  rcases family_descends (prefixWord ++ tailWord_268669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268686 : List Nat := [4, 1, 1, 4, 1, 1, 1, 6]
def baseStart_268686 : Nat := 118140960795 + 268686 * 2 ^ 59
def prefixEnd_268686 : Nat := 4983230072969 + 3 ^ 40 * 268686 * 2
def baseEnd_268686 : Nat := 81757074449802073178869

theorem tailTrace_268686 : CollatzResearch.WordTrace tailWord_268686 prefixEnd_268686 81757074449802073178869 := by
  unfold tailWord_268686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1224972938075498095073239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6533189003069323173723941 1224972938075498095073239)
  ·
    refine ⟨1837459407113247142609859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1224972938075498095073239 1837459407113247142609859)
    ·
      refine ⟨2756189110669870713914789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1837459407113247142609859 2756189110669870713914789)
      ·
        refine ⟨516785458250600758859023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2756189110669870713914789 516785458250600758859023)
        ·
          refine ⟨775178187375901138288535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516785458250600758859023 775178187375901138288535)
          ·
            refine ⟨1162767281063851707432803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 775178187375901138288535 1162767281063851707432803)
            ·
              refine ⟨1744150921595777561149205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1162767281063851707432803 1744150921595777561149205)
              ·
                refine ⟨81757074449802073178869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1744150921595777561149205 81757074449802073178869)
                ·
                  rfl

theorem cell19_268686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_268686 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268686 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268686 prefixEnd_268686 := by exact prefixLift 268686
  have htrace : WordTrace (prefixWord ++ tailWord_268686) baseStart_268686 baseEnd_268686 := by
    simpa [prefixWord, tailWord_268686, baseEnd_268686] using wordTrace_append hprefix tailTrace_268686
  have hstable : (prefixWord ++ tailWord_268686).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268686).length < 2 ^ (prefixWord ++ tailWord_268686).sum := by decide
  have hdescent : baseEnd_268686 < baseStart_268686 := by decide
  rcases family_descends (prefixWord ++ tailWord_268686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268707 : List Nat := [1, 1, 1, 4, 1, 4, 2, 5]
def baseStart_268707 : Nat := 118140960795 + 268707 * 2 ^ 59
def prefixEnd_268707 : Nat := 4983230072969 + 3 ^ 40 * 268707 * 2
def baseEnd_268707 : Nat := 81763464431280246712145

theorem tailTrace_268707 : CollatzResearch.WordTrace tailWord_268707 prefixEnd_268707 81763464431280246712145 := by
  unfold tailWord_268707
  simp only [CollatzResearch.WordTrace]
  refine ⟨9800549437527905347100375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6533699625018603564733583 9800549437527905347100375)
  ·
    refine ⟨14700824156291858020650563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9800549437527905347100375 14700824156291858020650563)
    ·
      refine ⟨22051236234437787030975845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14700824156291858020650563 22051236234437787030975845)
      ·
        refine ⟨4134606793957085068307971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22051236234437787030975845 4134606793957085068307971)
        ·
          refine ⟨6201910190935627602461957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4134606793957085068307971 6201910190935627602461957)
          ·
            refine ⟨1162858160800430175461617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6201910190935627602461957 1162858160800430175461617)
            ·
              refine ⟨872143620600322631596213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1162858160800430175461617 872143620600322631596213)
              ·
                refine ⟨81763464431280246712145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 872143620600322631596213 81763464431280246712145)
                ·
                  rfl

theorem cell19_268707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_268707 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268707 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268707 prefixEnd_268707 := by exact prefixLift 268707
  have htrace : WordTrace (prefixWord ++ tailWord_268707) baseStart_268707 baseEnd_268707 := by
    simpa [prefixWord, tailWord_268707, baseEnd_268707] using wordTrace_append hprefix tailTrace_268707
  have hstable : (prefixWord ++ tailWord_268707).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268707).length < 2 ^ (prefixWord ++ tailWord_268707).sum := by decide
  have hdescent : baseEnd_268707 < baseStart_268707 := by decide
  rcases family_descends (prefixWord ++ tailWord_268707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268726 : List Nat := [5, 1, 13]
def baseStart_268726 : Nat := 118140960795 + 268726 * 2 ^ 59
def prefixEnd_268726 : Nat := 4983230072969 + 3 ^ 40 * 268726 * 2
def baseEnd_268726 : Nat := 336498954086805894197

theorem tailTrace_268726 : CollatzResearch.WordTrace tailWord_268726 prefixEnd_268726 336498954086805894197 := by
  unfold tailWord_268726
  simp only [CollatzResearch.WordTrace]
  refine ⟨612577651528691974502627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6534161616306047728028021 612577651528691974502627)
  ·
    refine ⟨918866477293037961753941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 612577651528691974502627 918866477293037961753941)
    ·
      refine ⟨336498954086805894197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 13 918866477293037961753941 336498954086805894197)
      ·
        rfl

theorem cell19_268726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 13].length) (baseStart_268726 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268726 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268726 prefixEnd_268726 := by exact prefixLift 268726
  have htrace : WordTrace (prefixWord ++ tailWord_268726) baseStart_268726 baseEnd_268726 := by
    simpa [prefixWord, tailWord_268726, baseEnd_268726] using wordTrace_append hprefix tailTrace_268726
  have hstable : (prefixWord ++ tailWord_268726).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268726).length < 2 ^ (prefixWord ++ tailWord_268726).sum := by decide
  have hdescent : baseEnd_268726 < baseStart_268726 := by decide
  rcases family_descends (prefixWord ++ tailWord_268726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268737 : List Nat := [1, 2, 7, 1, 1, 2, 1, 4]
def baseStart_268737 : Nat := 118140960795 + 268737 * 2 ^ 59
def prefixEnd_268737 : Nat := 4983230072969 + 3 ^ 40 * 268737 * 2
def baseEnd_268737 : Nat := 81772592976249066045397

theorem tailTrace_268737 : CollatzResearch.WordTrace tailWord_268737 prefixEnd_268737 81772592976249066045397 := by
  unfold tailWord_268737
  simp only [CollatzResearch.WordTrace]
  refine ⟨9801643627419220470692465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6534429084946146980461643 9801643627419220470692465)
  ·
    refine ⟨7351232720564415353019349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9801643627419220470692465 7351232720564415353019349)
    ·
      refine ⟨172294516888228484836391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 7351232720564415353019349 172294516888228484836391)
      ·
        refine ⟨258441775332342727254587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172294516888228484836391 258441775332342727254587)
        ·
          refine ⟨387662662998514090881881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258441775332342727254587 387662662998514090881881)
          ·
            refine ⟨290746997248885568161411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387662662998514090881881 290746997248885568161411)
            ·
              refine ⟨436120495873328352242117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290746997248885568161411 436120495873328352242117)
              ·
                refine ⟨81772592976249066045397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 436120495873328352242117 81772592976249066045397)
                ·
                  rfl

theorem cell19_268737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 4].length) (baseStart_268737 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268737 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268737 prefixEnd_268737 := by exact prefixLift 268737
  have htrace : WordTrace (prefixWord ++ tailWord_268737) baseStart_268737 baseEnd_268737 := by
    simpa [prefixWord, tailWord_268737, baseEnd_268737] using wordTrace_append hprefix tailTrace_268737
  have hstable : (prefixWord ++ tailWord_268737).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268737).length < 2 ^ (prefixWord ++ tailWord_268737).sum := by decide
  have hdescent : baseEnd_268737 < baseStart_268737 := by decide
  rcases family_descends (prefixWord ++ tailWord_268737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268743 : List Nat := [1, 1, 4, 1, 1, 6, 1, 4]
def baseStart_268743 : Nat := 118140960795 + 268743 * 2 ^ 59
def prefixEnd_268743 : Nat := 4983230072969 + 3 ^ 40 * 268743 * 2
def baseEnd_268743 : Nat := 81774418685242829912047

theorem tailTrace_268743 : CollatzResearch.WordTrace tailWord_268743 prefixEnd_268743 81774418685242829912047 := by
  unfold tailWord_268743
  simp only [CollatzResearch.WordTrace]
  refine ⟨9801862465397483495410883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6534574976931655663607255 9801862465397483495410883)
  ·
    refine ⟨14702793698096225243116325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9801862465397483495410883 14702793698096225243116325)
    ·
      refine ⟨2756773818393042233084311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14702793698096225243116325 2756773818393042233084311)
      ·
        refine ⟨4135160727589563349626467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2756773818393042233084311 4135160727589563349626467)
        ·
          refine ⟨6202741091384345024439701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4135160727589563349626467 6202741091384345024439701)
          ·
            refine ⟨290753488658641173020611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6202741091384345024439701 290753488658641173020611)
            ·
              refine ⟨436130232987961759530917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290753488658641173020611 436130232987961759530917)
              ·
                refine ⟨81774418685242829912047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 436130232987961759530917 81774418685242829912047)
                ·
                  rfl

theorem cell19_268743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 4].length) (baseStart_268743 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268743 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268743 prefixEnd_268743 := by exact prefixLift 268743
  have htrace : WordTrace (prefixWord ++ tailWord_268743) baseStart_268743 baseEnd_268743 := by
    simpa [prefixWord, tailWord_268743, baseEnd_268743] using wordTrace_append hprefix tailTrace_268743
  have hstable : (prefixWord ++ tailWord_268743).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268743).length < 2 ^ (prefixWord ++ tailWord_268743).sum := by decide
  have hdescent : baseEnd_268743 < baseStart_268743 := by decide
  rcases family_descends (prefixWord ++ tailWord_268743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268745 : List Nat := [1, 2, 1, 1, 2, 1, 7, 4]
def baseStart_268745 : Nat := 118140960795 + 268745 * 2 ^ 59
def prefixEnd_268745 : Nat := 4983230072969 + 3 ^ 40 * 268745 * 2
def baseEnd_268745 : Nat := 81775027254907417867597

theorem tailTrace_268745 : CollatzResearch.WordTrace tailWord_268745 prefixEnd_268745 81775027254907417867597 := by
  unfold tailWord_268745
  simp only [CollatzResearch.WordTrace]
  refine ⟨9801935411390237836983689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6534623607593491891322459 9801935411390237836983689)
  ·
    refine ⟨7351451558542678377737767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9801935411390237836983689 7351451558542678377737767)
    ·
      refine ⟨11027177337814017566606651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7351451558542678377737767 11027177337814017566606651)
      ·
        refine ⟨16540766006721026349909977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11027177337814017566606651 16540766006721026349909977)
        ·
          refine ⟨12405574505040769762432483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16540766006721026349909977 12405574505040769762432483)
          ·
            refine ⟨18608361757561154643648725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12405574505040769762432483 18608361757561154643648725)
            ·
              refine ⟨436133478692839561960517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18608361757561154643648725 436133478692839561960517)
              ·
                refine ⟨81775027254907417867597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 436133478692839561960517 81775027254907417867597)
                ·
                  rfl

theorem cell19_268745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_268745 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268745 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268745 prefixEnd_268745 := by exact prefixLift 268745
  have htrace : WordTrace (prefixWord ++ tailWord_268745) baseStart_268745 baseEnd_268745 := by
    simpa [prefixWord, tailWord_268745, baseEnd_268745] using wordTrace_append hprefix tailTrace_268745
  have hstable : (prefixWord ++ tailWord_268745).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268745).length < 2 ^ (prefixWord ++ tailWord_268745).sum := by decide
  have hdescent : baseEnd_268745 < baseStart_268745 := by decide
  rcases family_descends (prefixWord ++ tailWord_268745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268762 : List Nat := [3, 1, 1, 2, 3, 1, 5, 3]
def baseStart_268762 : Nat := 118140960795 + 268762 * 2 ^ 59
def prefixEnd_268762 : Nat := 4983230072969 + 3 ^ 40 * 268762 * 2
def baseEnd_268762 : Nat := 81780200097056415489773

theorem tailTrace_268762 : CollatzResearch.WordTrace tailWord_268762 prefixEnd_268762 81780200097056415489773 := by
  unfold tailWord_268762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2450638863082162435088135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6535036968219099826901693 2450638863082162435088135)
  ·
    refine ⟨3675958294623243652632203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2450638863082162435088135 3675958294623243652632203)
    ·
      refine ⟨5513937441934865478948305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3675958294623243652632203 5513937441934865478948305)
      ·
        refine ⟨4135453081451149109211229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5513937441934865478948305 4135453081451149109211229)
        ·
          refine ⟨1550794905544180915954211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4135453081451149109211229 1550794905544180915954211)
          ·
            refine ⟨2326192358316271373931317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550794905544180915954211 2326192358316271373931317)
            ·
              refine ⟨218080533592150441306061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2326192358316271373931317 218080533592150441306061)
              ·
                refine ⟨81780200097056415489773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 218080533592150441306061 81780200097056415489773)
                ·
                  rfl

theorem cell19_268762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_268762 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268762 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268762 prefixEnd_268762 := by exact prefixLift 268762
  have htrace : WordTrace (prefixWord ++ tailWord_268762) baseStart_268762 baseEnd_268762 := by
    simpa [prefixWord, tailWord_268762, baseEnd_268762] using wordTrace_append hprefix tailTrace_268762
  have hstable : (prefixWord ++ tailWord_268762).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268762).length < 2 ^ (prefixWord ++ tailWord_268762).sum := by decide
  have hdescent : baseEnd_268762 < baseStart_268762 := by decide
  rcases family_descends (prefixWord ++ tailWord_268762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268781 : List Nat := [1, 5, 1, 3, 1, 2, 6]
def baseStart_268781 : Nat := 118140960795 + 268781 * 2 ^ 59
def prefixEnd_268781 : Nat := 4983230072969 + 3 ^ 40 * 268781 * 2
def baseEnd_268781 : Nat := 27261993836290000355833

theorem tailTrace_268781 : CollatzResearch.WordTrace tailWord_268781 prefixEnd_268781 27261993836290000355833 := by
  unfold tailWord_268781
  simp only [CollatzResearch.WordTrace]
  refine ⟨9803248439259815985294197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6535498959506543990196131 9803248439259815985294197)
  ·
    refine ⟨919054541180607748621331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9803248439259815985294197 919054541180607748621331)
    ·
      refine ⟨1378581811770911622931997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 919054541180607748621331 1378581811770911622931997)
      ·
        refine ⟨516968179414091858599499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1378581811770911622931997 516968179414091858599499)
        ·
          refine ⟨775452269121137787899249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516968179414091858599499 775452269121137787899249)
          ·
            refine ⟨581589201840853340924437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 775452269121137787899249 581589201840853340924437)
            ·
              refine ⟨27261993836290000355833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 581589201840853340924437 27261993836290000355833)
              ·
                rfl

theorem cell19_268781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 6].length) (baseStart_268781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268781 prefixEnd_268781 := by exact prefixLift 268781
  have htrace : WordTrace (prefixWord ++ tailWord_268781) baseStart_268781 baseEnd_268781 := by
    simpa [prefixWord, tailWord_268781, baseEnd_268781] using wordTrace_append hprefix tailTrace_268781
  have hstable : (prefixWord ++ tailWord_268781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268781).length < 2 ^ (prefixWord ++ tailWord_268781).sum := by decide
  have hdescent : baseEnd_268781 < baseStart_268781 := by decide
  rcases family_descends (prefixWord ++ tailWord_268781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268813 : List Nat := [1, 7, 1, 1, 1, 3, 2, 3]
def baseStart_268813 : Nat := 118140960795 + 268813 * 2 ^ 59
def prefixEnd_268813 : Nat := 4983230072969 + 3 ^ 40 * 268813 * 2
def baseEnd_268813 : Nat := 81795718623503408356301

theorem tailTrace_268813 : CollatzResearch.WordTrace tailWord_268813 prefixEnd_268813 81795718623503408356301 := by
  unfold tailWord_268813
  simp only [CollatzResearch.WordTrace]
  refine ⟨9804415575143885450459093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6536277050095923633639395 9804415575143885450459093)
  ·
    refine ⟨229790990042434815245135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 9804415575143885450459093 229790990042434815245135)
    ·
      refine ⟨344686485063652222867703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229790990042434815245135 344686485063652222867703)
      ·
        refine ⟨517029727595478334301555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344686485063652222867703 517029727595478334301555)
        ·
          refine ⟨775544591393217501452333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517029727595478334301555 775544591393217501452333)
          ·
            refine ⟨290829221772456563044625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 775544591393217501452333 290829221772456563044625)
            ·
              refine ⟨218121916329342422283469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290829221772456563044625 218121916329342422283469)
              ·
                refine ⟨81795718623503408356301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 218121916329342422283469 81795718623503408356301)
                ·
                  rfl

theorem cell19_268813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 3].length) (baseStart_268813 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268813 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268813 prefixEnd_268813 := by exact prefixLift 268813
  have htrace : WordTrace (prefixWord ++ tailWord_268813) baseStart_268813 baseEnd_268813 := by
    simpa [prefixWord, tailWord_268813, baseEnd_268813] using wordTrace_append hprefix tailTrace_268813
  have hstable : (prefixWord ++ tailWord_268813).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268813).length < 2 ^ (prefixWord ++ tailWord_268813).sum := by decide
  have hdescent : baseEnd_268813 < baseStart_268813 := by decide
  rcases family_descends (prefixWord ++ tailWord_268813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268821 : List Nat := [1, 3, 2, 1, 3, 1, 3, 5]
def baseStart_268821 : Nat := 118140960795 + 268821 * 2 ^ 59
def prefixEnd_268821 : Nat := 4983230072969 + 3 ^ 40 * 268821 * 2
def baseEnd_268821 : Nat := 81798152902161760178501

theorem tailTrace_268821 : CollatzResearch.WordTrace tailWord_268821 prefixEnd_268821 81798152902161760178501 := by
  unfold tailWord_268821
  simp only [CollatzResearch.WordTrace]
  refine ⟨9804707359114902816750317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6536471572743268544500211 9804707359114902816750317)
  ·
    refine ⟨3676765259668088556281369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9804707359114902816750317 3676765259668088556281369)
    ·
      refine ⟨2757573944751066417211027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3676765259668088556281369 2757573944751066417211027)
      ·
        refine ⟨4136360917126599625816541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2757573944751066417211027 4136360917126599625816541)
        ·
          refine ⟨1551135343922474859681203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4136360917126599625816541 1551135343922474859681203)
          ·
            refine ⟨2326703015883712289521805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551135343922474859681203 2326703015883712289521805)
            ·
              refine ⟨872513630956392108570677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2326703015883712289521805 872513630956392108570677)
              ·
                refine ⟨81798152902161760178501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 872513630956392108570677 81798152902161760178501)
                ·
                  rfl

theorem cell19_268821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_268821 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268821 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268821 prefixEnd_268821 := by exact prefixLift 268821
  have htrace : WordTrace (prefixWord ++ tailWord_268821) baseStart_268821 baseEnd_268821 := by
    simpa [prefixWord, tailWord_268821, baseEnd_268821] using wordTrace_append hprefix tailTrace_268821
  have hstable : (prefixWord ++ tailWord_268821).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268821).length < 2 ^ (prefixWord ++ tailWord_268821).sum := by decide
  have hdescent : baseEnd_268821 < baseStart_268821 := by decide
  rcases family_descends (prefixWord ++ tailWord_268821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268836 : List Nat := [2, 3, 1, 5, 1, 2, 5]
def baseStart_268836 : Nat := 118140960795 + 268836 * 2 ^ 59
def prefixEnd_268836 : Nat := 4983230072969 + 3 ^ 40 * 268836 * 2
def baseEnd_268836 : Nat := 27267572391548723281709

theorem tailTrace_268836 : CollatzResearch.WordTrace tailWord_268836 prefixEnd_268836 27267572391548723281709 := by
  unfold tailWord_268836
  simp only [CollatzResearch.WordTrace]
  refine ⟨4902627227030280189273181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6536836302707040252364241 4902627227030280189273181)
  ·
    refine ⟨1838485210136355070977443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4902627227030280189273181 1838485210136355070977443)
    ·
      refine ⟨2757727815204532606466165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1838485210136355070977443 2757727815204532606466165)
      ·
        refine ⟨258536982675424931856203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2757727815204532606466165 258536982675424931856203)
        ·
          refine ⟨387805474013137397784305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258536982675424931856203 387805474013137397784305)
          ·
            refine ⟨290854105509853048338229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387805474013137397784305 290854105509853048338229)
            ·
              refine ⟨27267572391548723281709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 290854105509853048338229 27267572391548723281709)
              ·
                rfl

theorem cell19_268836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 5].length) (baseStart_268836 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268836 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268836 prefixEnd_268836 := by exact prefixLift 268836
  have htrace : WordTrace (prefixWord ++ tailWord_268836) baseStart_268836 baseEnd_268836 := by
    simpa [prefixWord, tailWord_268836, baseEnd_268836] using wordTrace_append hprefix tailTrace_268836
  have hstable : (prefixWord ++ tailWord_268836).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268836).length < 2 ^ (prefixWord ++ tailWord_268836).sum := by decide
  have hdescent : baseEnd_268836 < baseStart_268836 := by decide
  rcases family_descends (prefixWord ++ tailWord_268836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268878 : List Nat := [4, 1, 1, 1, 1, 2, 4, 5]
def baseStart_268878 : Nat := 118140960795 + 268878 * 2 ^ 59
def prefixEnd_268878 : Nat := 4983230072969 + 3 ^ 40 * 268878 * 2
def baseEnd_268878 : Nat := 81815497137602516911679

theorem tailTrace_268878 : CollatzResearch.WordTrace tailWord_268878 prefixEnd_268878 81815497137602516911679 := by
  unfold tailWord_268878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1225848289988550193946911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6537857546605601034383525 1225848289988550193946911)
  ·
    refine ⟨1838772434982825290920367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1225848289988550193946911 1838772434982825290920367)
    ·
      refine ⟨2758158652474237936380551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1838772434982825290920367 2758158652474237936380551)
      ·
        refine ⟨4137237978711356904570827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2758158652474237936380551 4137237978711356904570827)
        ·
          refine ⟨6205856968067035356856241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4137237978711356904570827 6205856968067035356856241)
          ·
            refine ⟨4654392726050276517642181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6205856968067035356856241 4654392726050276517642181)
            ·
              refine ⟨872698636134426847057909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4654392726050276517642181 872698636134426847057909)
              ·
                refine ⟨81815497137602516911679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 872698636134426847057909 81815497137602516911679)
                ·
                  rfl

theorem cell19_268878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_268878 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268878 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268878 prefixEnd_268878 := by exact prefixLift 268878
  have htrace : WordTrace (prefixWord ++ tailWord_268878) baseStart_268878 baseEnd_268878 := by
    simpa [prefixWord, tailWord_268878, baseEnd_268878] using wordTrace_append hprefix tailTrace_268878
  have hstable : (prefixWord ++ tailWord_268878).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268878).length < 2 ^ (prefixWord ++ tailWord_268878).sum := by decide
  have hdescent : baseEnd_268878 < baseStart_268878 := by decide
  rcases family_descends (prefixWord ++ tailWord_268878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268912 : List Nat := [2, 1, 1, 1, 8, 1, 1, 4]
def baseStart_268912 : Nat := 118140960795 + 268912 * 2 ^ 59
def prefixEnd_268912 : Nat := 4983230072969 + 3 ^ 40 * 268912 * 2
def baseEnd_268912 : Nat := 81825842821900512156031

theorem tailTrace_268912 : CollatzResearch.WordTrace tailWord_268912 prefixEnd_268912 81825842821900512156031 := by
  unfold tailWord_268912
  simp only [CollatzResearch.WordTrace]
  refine ⟨4904013200892612679156495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6538684267856816905541993 4904013200892612679156495)
  ·
    refine ⟨7356019801338919018734743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4904013200892612679156495 7356019801338919018734743)
    ·
      refine ⟨11034029702008378528102115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7356019801338919018734743 11034029702008378528102115)
      ·
        refine ⟨16551044553012567792153173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11034029702008378528102115 16551044553012567792153173)
        ·
          refine ⟨193957553355616028814295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 16551044553012567792153173 193957553355616028814295)
          ·
            refine ⟨290936330033424043221443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193957553355616028814295 290936330033424043221443)
            ·
              refine ⟨436404495050136064832165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290936330033424043221443 436404495050136064832165)
              ·
                refine ⟨81825842821900512156031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 436404495050136064832165 81825842821900512156031)
                ·
                  rfl

theorem cell19_268912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 4].length) (baseStart_268912 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268912 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268912 prefixEnd_268912 := by exact prefixLift 268912
  have htrace : WordTrace (prefixWord ++ tailWord_268912) baseStart_268912 baseEnd_268912 := by
    simpa [prefixWord, tailWord_268912, baseEnd_268912] using wordTrace_append hprefix tailTrace_268912
  have hstable : (prefixWord ++ tailWord_268912).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268912).length < 2 ^ (prefixWord ++ tailWord_268912).sum := by decide
  have hdescent : baseEnd_268912 < baseStart_268912 := by decide
  rcases family_descends (prefixWord ++ tailWord_268912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268933 : List Nat := [1, 3, 1, 1, 4, 3, 3, 3]
def baseStart_268933 : Nat := 118140960795 + 268933 * 2 ^ 59
def prefixEnd_268933 : Nat := 4983230072969 + 3 ^ 40 * 268933 * 2
def baseEnd_268933 : Nat := 81832232803378685689307

theorem tailTrace_268933 : CollatzResearch.WordTrace tailWord_268933 prefixEnd_268933 81832232803378685689307 := by
  unfold tailWord_268933
  simp only [CollatzResearch.WordTrace]
  refine ⟨9808792334709145944827453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6539194889806097296551635 9808792334709145944827453)
  ·
    refine ⟨3678297125515929729310295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9808792334709145944827453 3678297125515929729310295)
    ·
      refine ⟨5517445688273894593965443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3678297125515929729310295 5517445688273894593965443)
      ·
        refine ⟨8276168532410841890948165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5517445688273894593965443 8276168532410841890948165)
        ·
          refine ⟨1551781599827032854552781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8276168532410841890948165 1551781599827032854552781)
          ·
            refine ⟨581918099935137320457293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1551781599827032854552781 581918099935137320457293)
            ·
              refine ⟨218219287475676495171485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 581918099935137320457293 218219287475676495171485)
              ·
                refine ⟨81832232803378685689307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 218219287475676495171485 81832232803378685689307)
                ·
                  rfl

theorem cell19_268933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 3].length) (baseStart_268933 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268933 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268933 prefixEnd_268933 := by exact prefixLift 268933
  have htrace : WordTrace (prefixWord ++ tailWord_268933) baseStart_268933 baseEnd_268933 := by
    simpa [prefixWord, tailWord_268933, baseEnd_268933] using wordTrace_append hprefix tailTrace_268933
  have hstable : (prefixWord ++ tailWord_268933).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268933).length < 2 ^ (prefixWord ++ tailWord_268933).sum := by decide
  have hdescent : baseEnd_268933 < baseStart_268933 := by decide
  rcases family_descends (prefixWord ++ tailWord_268933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268992 : List Nat := [2, 1, 1, 2, 4, 3, 1, 5]
def baseStart_268992 : Nat := 118140960795 + 268992 * 2 ^ 59
def prefixEnd_268992 : Nat := 4983230072969 + 3 ^ 40 * 268992 * 2
def baseEnd_268992 : Nat := 81850185608484030378035

theorem tailTrace_268992 : CollatzResearch.WordTrace tailWord_268992 prefixEnd_268992 81850185608484030378035 := by
  unfold tailWord_268992
  simp only [CollatzResearch.WordTrace]
  refine ⟨4905472120747699510612615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6540629494330266014150153 4905472120747699510612615)
  ·
    refine ⟨7358208181121549265918923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4905472120747699510612615 7358208181121549265918923)
    ·
      refine ⟨11037312271682323898878385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7358208181121549265918923 11037312271682323898878385)
      ·
        refine ⟨8277984203761742924158789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11037312271682323898878385 8277984203761742924158789)
        ·
          refine ⟨1552122038205326798279773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8277984203761742924158789 1552122038205326798279773)
          ·
            refine ⟨582045764326997549354915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1552122038205326798279773 582045764326997549354915)
            ·
              refine ⟨873068646490496324032373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 582045764326997549354915 873068646490496324032373)
              ·
                refine ⟨81850185608484030378035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 873068646490496324032373 81850185608484030378035)
                ·
                  rfl

theorem cell19_268992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_268992 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_268992 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_268992 prefixEnd_268992 := by exact prefixLift 268992
  have htrace : WordTrace (prefixWord ++ tailWord_268992) baseStart_268992 baseEnd_268992 := by
    simpa [prefixWord, tailWord_268992, baseEnd_268992] using wordTrace_append hprefix tailTrace_268992
  have hstable : (prefixWord ++ tailWord_268992).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268992).length < 2 ^ (prefixWord ++ tailWord_268992).sum := by decide
  have hdescent : baseEnd_268992 < baseStart_268992 := by decide
  rcases family_descends (prefixWord ++ tailWord_268992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269005 : List Nat := [1, 6, 2, 1, 3, 1, 5]
def baseStart_269005 : Nat := 118140960795 + 269005 * 2 ^ 59
def prefixEnd_269005 : Nat := 4983230072969 + 3 ^ 40 * 269005 * 2
def baseEnd_269005 : Nat := 27284713770434617363037

theorem tailTrace_269005 : CollatzResearch.WordTrace tailWord_269005 prefixEnd_269005 27284713770434617363037 := by
  unfold tailWord_269005
  simp only [CollatzResearch.WordTrace]
  refine ⟨9811418390448302241448469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6540945593632201494298979 9811418390448302241448469)
  ·
    refine ⟨459910237052264167567897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9811418390448302241448469 459910237052264167567897)
    ·
      refine ⟨344932677789198125675923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 459910237052264167567897 344932677789198125675923)
      ·
        refine ⟨517399016683797188513885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344932677789198125675923 517399016683797188513885)
        ·
          refine ⟨194024631256423945692707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 517399016683797188513885 194024631256423945692707)
          ·
            refine ⟨291036946884635918539061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194024631256423945692707 291036946884635918539061)
            ·
              refine ⟨27284713770434617363037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 291036946884635918539061 27284713770434617363037)
              ·
                rfl

theorem cell19_269005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 5].length) (baseStart_269005 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269005 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269005 prefixEnd_269005 := by exact prefixLift 269005
  have htrace : WordTrace (prefixWord ++ tailWord_269005) baseStart_269005 baseEnd_269005 := by
    simpa [prefixWord, tailWord_269005, baseEnd_269005] using wordTrace_append hprefix tailTrace_269005
  have hstable : (prefixWord ++ tailWord_269005).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269005).length < 2 ^ (prefixWord ++ tailWord_269005).sum := by decide
  have hdescent : baseEnd_269005 < baseStart_269005 := by decide
  rcases family_descends (prefixWord ++ tailWord_269005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269087 : List Nat := [1, 1, 2, 4, 2, 2, 3, 4]
def baseStart_269087 : Nat := 118140960795 + 269087 * 2 ^ 59
def prefixEnd_269087 : Nat := 4983230072969 + 3 ^ 40 * 269087 * 2
def baseEnd_269087 : Nat := 81879092667551958266665

theorem tailTrace_269087 : CollatzResearch.WordTrace tailWord_269087 prefixEnd_269087 81879092667551958266665 := by
  unfold tailWord_269087
  simp only [CollatzResearch.WordTrace]
  refine ⟨9814409176151230245933515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6542939450767486830622343 9814409176151230245933515)
  ·
    refine ⟨14721613764226845368900273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9814409176151230245933515 14721613764226845368900273)
    ·
      refine ⟨11041210323170134026675205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14721613764226845368900273 11041210323170134026675205)
      ·
        refine ⟨2070226935594400130001601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11041210323170134026675205 2070226935594400130001601)
        ·
          refine ⟨1552670201695800097501201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2070226935594400130001601 1552670201695800097501201)
          ·
            refine ⟨1164502651271850073125901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1552670201695800097501201 1164502651271850073125901)
            ·
              refine ⟨436688494226943777422213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1164502651271850073125901 436688494226943777422213)
              ·
                refine ⟨81879092667551958266665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 436688494226943777422213 81879092667551958266665)
                ·
                  rfl

theorem cell19_269087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_269087 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269087 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269087 prefixEnd_269087 := by exact prefixLift 269087
  have htrace : WordTrace (prefixWord ++ tailWord_269087) baseStart_269087 baseEnd_269087 := by
    simpa [prefixWord, tailWord_269087, baseEnd_269087] using wordTrace_append hprefix tailTrace_269087
  have hstable : (prefixWord ++ tailWord_269087).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269087).length < 2 ^ (prefixWord ++ tailWord_269087).sum := by decide
  have hdescent : baseEnd_269087 < baseStart_269087 := by decide
  rcases family_descends (prefixWord ++ tailWord_269087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269102 : List Nat := [4, 1, 3, 2, 1, 2, 3, 3]
def baseStart_269102 : Nat := 118140960795 + 269102 * 2 ^ 59
def prefixEnd_269102 : Nat := 4983230072969 + 3 ^ 40 * 269102 * 2
def baseEnd_269102 : Nat := 81883656940036367933291

theorem tailTrace_269102 : CollatzResearch.WordTrace tailWord_269102 prefixEnd_269102 81883656940036367933291 := by
  unfold tailWord_269102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1226869533887110975966195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6543304180731258538486373 1226869533887110975966195)
  ·
    refine ⟨1840304300830666463949293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1226869533887110975966195 1840304300830666463949293)
    ·
      refine ⟨690114112811499923980985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1840304300830666463949293 690114112811499923980985)
      ·
        refine ⟨517585584608624942985739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 690114112811499923980985 517585584608624942985739)
        ·
          refine ⟨776378376912937414478609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517585584608624942985739 776378376912937414478609)
          ·
            refine ⟨582283782684703060858957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 776378376912937414478609 582283782684703060858957)
            ·
              refine ⟨218356418506763647822109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 582283782684703060858957 218356418506763647822109)
              ·
                refine ⟨81883656940036367933291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 218356418506763647822109 81883656940036367933291)
                ·
                  rfl

theorem cell19_269102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_269102 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269102 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269102 prefixEnd_269102 := by exact prefixLift 269102
  have htrace : WordTrace (prefixWord ++ tailWord_269102) baseStart_269102 baseEnd_269102 := by
    simpa [prefixWord, tailWord_269102, baseEnd_269102] using wordTrace_append hprefix tailTrace_269102
  have hstable : (prefixWord ++ tailWord_269102).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269102).length < 2 ^ (prefixWord ++ tailWord_269102).sum := by decide
  have hdescent : baseEnd_269102 < baseStart_269102 := by decide
  rcases family_descends (prefixWord ++ tailWord_269102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269163 : List Nat := [1, 1, 1, 1, 2, 2, 8, 3]
def baseStart_269163 : Nat := 118140960795 + 269163 * 2 ^ 59
def prefixEnd_269163 : Nat := 4983230072969 + 3 ^ 40 * 269163 * 2
def baseEnd_269163 : Nat := 81902218314806300577569

theorem tailTrace_269163 : CollatzResearch.WordTrace tailWord_269163 prefixEnd_269163 81902218314806300577569 := by
  unfold tailWord_269163
  simp only [CollatzResearch.WordTrace]
  refine ⟨9817181123875895225700143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6544787415917263483800095 9817181123875895225700143)
  ·
    refine ⟨14725771685813842838550215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9817181123875895225700143 14725771685813842838550215)
    ·
      refine ⟨22088657528720764257825323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14725771685813842838550215 22088657528720764257825323)
      ·
        refine ⟨33132986293081146386737985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22088657528720764257825323 33132986293081146386737985)
        ·
          refine ⟨24849739719810859790053489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33132986293081146386737985 24849739719810859790053489)
          ·
            refine ⟨18637304789858144842540117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24849739719810859790053489 18637304789858144842540117)
            ·
              refine ⟨218405915506150134873517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 18637304789858144842540117 218405915506150134873517)
              ·
                refine ⟨81902218314806300577569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 218405915506150134873517 81902218314806300577569)
                ·
                  rfl

theorem cell19_269163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 3].length) (baseStart_269163 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269163 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269163 prefixEnd_269163 := by exact prefixLift 269163
  have htrace : WordTrace (prefixWord ++ tailWord_269163) baseStart_269163 baseEnd_269163 := by
    simpa [prefixWord, tailWord_269163, baseEnd_269163] using wordTrace_append hprefix tailTrace_269163
  have hstable : (prefixWord ++ tailWord_269163).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269163).length < 2 ^ (prefixWord ++ tailWord_269163).sum := by decide
  have hdescent : baseEnd_269163 < baseStart_269163 := by decide
  rcases family_descends (prefixWord ++ tailWord_269163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269241 : List Nat := [1, 2, 1, 4, 2, 9]
def baseStart_269241 : Nat := 118140960795 + 269241 * 2 ^ 59
def prefixEnd_269241 : Nat := 4983230072969 + 3 ^ 40 * 269241 * 2
def baseEnd_269241 : Nat := 9102883614636136760447

theorem tailTrace_269241 : CollatzResearch.WordTrace tailWord_269241 prefixEnd_269241 9102883614636136760447 := by
  unfold tailWord_269241
  simp only [CollatzResearch.WordTrace]
  refine ⟨9820026017593314547039577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6546684011728876364693051 9820026017593314547039577)
  ·
    refine ⟨7365019513194985910279683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9820026017593314547039577 7365019513194985910279683)
    ·
      refine ⟨11047529269792478865419525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7365019513194985910279683 11047529269792478865419525)
      ·
        refine ⟨2071411738086089787266161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11047529269792478865419525 2071411738086089787266161)
        ·
          refine ⟨1553558803564567340449621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2071411738086089787266161 1553558803564567340449621)
          ·
            refine ⟨9102883614636136760447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1553558803564567340449621 9102883614636136760447)
            ·
              rfl

theorem cell19_269241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 9].length) (baseStart_269241 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269241 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269241 prefixEnd_269241 := by exact prefixLift 269241
  have htrace : WordTrace (prefixWord ++ tailWord_269241) baseStart_269241 baseEnd_269241 := by
    simpa [prefixWord, tailWord_269241, baseEnd_269241] using wordTrace_append hprefix tailTrace_269241
  have hstable : (prefixWord ++ tailWord_269241).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269241).length < 2 ^ (prefixWord ++ tailWord_269241).sum := by decide
  have hdescent : baseEnd_269241 < baseStart_269241 := by decide
  rcases family_descends (prefixWord ++ tailWord_269241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269252 : List Nat := [2, 3, 3, 3, 2, 1, 1, 4]
def baseStart_269252 : Nat := 118140960795 + 269252 * 2 ^ 59
def prefixEnd_269252 : Nat := 4983230072969 + 3 ^ 40 * 269252 * 2
def baseEnd_269252 : Nat := 81929299664880464599549

theorem tailTrace_269252 : CollatzResearch.WordTrace tailWord_269252 prefixEnd_269252 81929299664880464599549 := by
  unfold tailWord_269252
  simp only [CollatzResearch.WordTrace]
  refine ⟨4910213610276731712845005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6546951480368975617126673 4910213610276731712845005)
  ·
    refine ⟨1841330103853774392316877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4910213610276731712845005 1841330103853774392316877)
    ·
      refine ⟨690498788945165397118829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1841330103853774392316877 690498788945165397118829)
      ·
        refine ⟨258937045854437023919561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 690498788945165397118829 258937045854437023919561)
        ·
          refine ⟨194202784390827767939671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258937045854437023919561 194202784390827767939671)
          ·
            refine ⟨291304176586241651909507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194202784390827767939671 291304176586241651909507)
            ·
              refine ⟨436956264879362477864261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291304176586241651909507 436956264879362477864261)
              ·
                refine ⟨81929299664880464599549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 436956264879362477864261 81929299664880464599549)
                ·
                  rfl

theorem cell19_269252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 4].length) (baseStart_269252 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269252 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269252 prefixEnd_269252 := by exact prefixLift 269252
  have htrace : WordTrace (prefixWord ++ tailWord_269252) baseStart_269252 baseEnd_269252 := by
    simpa [prefixWord, tailWord_269252, baseEnd_269252] using wordTrace_append hprefix tailTrace_269252
  have hstable : (prefixWord ++ tailWord_269252).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269252).length < 2 ^ (prefixWord ++ tailWord_269252).sum := by decide
  have hdescent : baseEnd_269252 < baseStart_269252 := by decide
  rcases family_descends (prefixWord ++ tailWord_269252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269256 : List Nat := [2, 1, 3, 1, 5, 2, 1, 4]
def baseStart_269256 : Nat := 118140960795 + 269256 * 2 ^ 59
def prefixEnd_269256 : Nat := 4983230072969 + 3 ^ 40 * 269256 * 2
def baseEnd_269256 : Nat := 81930516804209640510649

theorem tailTrace_269256 : CollatzResearch.WordTrace tailWord_269256 prefixEnd_269256 81930516804209640510649 := by
  unfold tailWord_269256
  simp only [CollatzResearch.WordTrace]
  refine ⟨4910286556269486054417811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6547048741692648072557081 4910286556269486054417811)
  ·
    refine ⟨7365429834404229081626717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4910286556269486054417811 7365429834404229081626717)
    ·
      refine ⟨2762036187901585905610019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7365429834404229081626717 2762036187901585905610019)
      ·
        refine ⟨4143054281852378858415029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2762036187901585905610019 4143054281852378858415029)
        ·
          refine ⟨388411338923660517976409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4143054281852378858415029 388411338923660517976409)
          ·
            refine ⟨291308504192745388482307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 388411338923660517976409 291308504192745388482307)
            ·
              refine ⟨436962756289118082723461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291308504192745388482307 436962756289118082723461)
              ·
                refine ⟨81930516804209640510649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 436962756289118082723461 81930516804209640510649)
                ·
                  rfl

theorem cell19_269256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_269256 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269256 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269256 prefixEnd_269256 := by exact prefixLift 269256
  have htrace : WordTrace (prefixWord ++ tailWord_269256) baseStart_269256 baseEnd_269256 := by
    simpa [prefixWord, tailWord_269256, baseEnd_269256] using wordTrace_append hprefix tailTrace_269256
  have hstable : (prefixWord ++ tailWord_269256).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269256).length < 2 ^ (prefixWord ++ tailWord_269256).sum := by decide
  have hdescent : baseEnd_269256 < baseStart_269256 := by decide
  rcases family_descends (prefixWord ++ tailWord_269256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269317 : List Nat := [1, 3, 1, 1, 2, 3, 2, 6]
def baseStart_269317 : Nat := 118140960795 + 269317 * 2 ^ 59
def prefixEnd_269317 : Nat := 4983230072969 + 3 ^ 40 * 269317 * 2
def baseEnd_269317 : Nat := 81949078178979573154927

theorem tailTrace_269317 : CollatzResearch.WordTrace tailWord_269317 prefixEnd_269317 81949078178979573154927 := by
  unfold tailWord_269317
  simp only [CollatzResearch.WordTrace]
  refine ⟨9822797965317979526806205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6548531976878653017870803 9822797965317979526806205)
  ·
    refine ⟨3683549236994242322552327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9822797965317979526806205 3683549236994242322552327)
    ·
      refine ⟨5525323855491363483828491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3683549236994242322552327 5525323855491363483828491)
      ·
        refine ⟨8287985783237045225742737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5525323855491363483828491 8287985783237045225742737)
        ·
          refine ⟨6215989337427783919307053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8287985783237045225742737 6215989337427783919307053)
          ·
            refine ⟨2330996001535418969740145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6215989337427783919307053 2330996001535418969740145)
            ·
              refine ⟨1748247001151564227305109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2330996001535418969740145 1748247001151564227305109)
              ·
                refine ⟨81949078178979573154927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1748247001151564227305109 81949078178979573154927)
                ·
                  rfl

theorem cell19_269317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_269317 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269317 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269317 prefixEnd_269317 := by exact prefixLift 269317
  have htrace : WordTrace (prefixWord ++ tailWord_269317) baseStart_269317 baseEnd_269317 := by
    simpa [prefixWord, tailWord_269317, baseEnd_269317] using wordTrace_append hprefix tailTrace_269317
  have hstable : (prefixWord ++ tailWord_269317).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269317).length < 2 ^ (prefixWord ++ tailWord_269317).sum := by decide
  have hdescent : baseEnd_269317 < baseStart_269317 := by decide
  rcases family_descends (prefixWord ++ tailWord_269317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269351 : List Nat := [1, 1, 7, 1, 1, 3, 5]
def baseStart_269351 : Nat := 118140960795 + 269351 * 2 ^ 59
def prefixEnd_269351 : Nat := 4983230072969 + 3 ^ 40 * 269351 * 2
def baseEnd_269351 : Nat := 27319807954425856133093

theorem tailTrace_269351 : CollatzResearch.WordTrace tailWord_269351 prefixEnd_269351 27319807954425856133093 := by
  unfold tailWord_269351
  simp only [CollatzResearch.WordTrace]
  refine ⟨9824038047194803333543907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6549358698129868889029271 9824038047194803333543907)
  ·
    refine ⟨14736057070792205000315861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9824038047194803333543907 14736057070792205000315861)
    ·
      refine ⟨345376337596692304694903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 14736057070792205000315861 345376337596692304694903)
      ·
        refine ⟨518064506395038457042355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345376337596692304694903 518064506395038457042355)
        ·
          refine ⟨777096759592557685563533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518064506395038457042355 777096759592557685563533)
          ·
            refine ⟨291411284847209132086325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 777096759592557685563533 291411284847209132086325)
            ·
              refine ⟨27319807954425856133093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 291411284847209132086325 27319807954425856133093)
              ·
                rfl

theorem cell19_269351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 5].length) (baseStart_269351 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269351 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269351 prefixEnd_269351 := by exact prefixLift 269351
  have htrace : WordTrace (prefixWord ++ tailWord_269351) baseStart_269351 baseEnd_269351 := by
    simpa [prefixWord, tailWord_269351, baseEnd_269351] using wordTrace_append hprefix tailTrace_269351
  have hstable : (prefixWord ++ tailWord_269351).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269351).length < 2 ^ (prefixWord ++ tailWord_269351).sum := by decide
  have hdescent : baseEnd_269351 < baseStart_269351 := by decide
  rcases family_descends (prefixWord ++ tailWord_269351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269372 : List Nat := [2, 2, 2, 2, 2, 3, 2, 4]
def baseStart_269372 : Nat := 118140960795 + 269372 * 2 ^ 59
def prefixEnd_269372 : Nat := 4983230072969 + 3 ^ 40 * 269372 * 2
def baseEnd_269372 : Nat := 81965813844755741932555

theorem tailTrace_269372 : CollatzResearch.WordTrace tailWord_269372 prefixEnd_269372 81965813844755741932555 := by
  unfold tailWord_269372
  simp only [CollatzResearch.WordTrace]
  refine ⟨4912401990059361960029185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6549869320079149280038913 4912401990059361960029185)
  ·
    refine ⟨3684301492544521470021889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4912401990059361960029185 3684301492544521470021889)
    ·
      refine ⟨2763226119408391102516417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3684301492544521470021889 2763226119408391102516417)
      ·
        refine ⟨2072419589556293326887313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2763226119408391102516417 2072419589556293326887313)
        ·
          refine ⟨1554314692167219995165485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2072419589556293326887313 1554314692167219995165485)
          ·
            refine ⟨582868009562707498187057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1554314692167219995165485 582868009562707498187057)
            ·
              refine ⟨437151007172030623640293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 582868009562707498187057 437151007172030623640293)
              ·
                refine ⟨81965813844755741932555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 437151007172030623640293 81965813844755741932555)
                ·
                  rfl

theorem cell19_269372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_269372 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269372 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269372 prefixEnd_269372 := by exact prefixLift 269372
  have htrace : WordTrace (prefixWord ++ tailWord_269372) baseStart_269372 baseEnd_269372 := by
    simpa [prefixWord, tailWord_269372, baseEnd_269372] using wordTrace_append hprefix tailTrace_269372
  have hstable : (prefixWord ++ tailWord_269372).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269372).length < 2 ^ (prefixWord ++ tailWord_269372).sum := by decide
  have hdescent : baseEnd_269372 < baseStart_269372 := by decide
  rcases family_descends (prefixWord ++ tailWord_269372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269393 : List Nat := [1, 2, 2, 1, 3, 1, 4, 5]
def baseStart_269393 : Nat := 118140960795 + 269393 * 2 ^ 59
def prefixEnd_269393 : Nat := 4983230072969 + 3 ^ 40 * 269393 * 2
def baseEnd_269393 : Nat := 81972203826233915465831

theorem tailTrace_269393 : CollatzResearch.WordTrace tailWord_269393 prefixEnd_269393 81972203826233915465831 := by
  unfold tailWord_269393
  simp only [CollatzResearch.WordTrace]
  refine ⟨9825569913042644506572833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6550379942028429671048555 9825569913042644506572833)
  ·
    refine ⟨7369177434781983379929625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9825569913042644506572833 7369177434781983379929625)
    ·
      refine ⟨5526883076086487534947219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7369177434781983379929625 5526883076086487534947219)
      ·
        refine ⟨8290324614129731302420829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5526883076086487534947219 8290324614129731302420829)
        ·
          refine ⟨3108871730298649238407811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8290324614129731302420829 3108871730298649238407811)
          ·
            refine ⟨4663307595447973857611717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3108871730298649238407811 4663307595447973857611717)
            ·
              refine ⟨874370174146495098302197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4663307595447973857611717 874370174146495098302197)
              ·
                refine ⟨81972203826233915465831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 874370174146495098302197 81972203826233915465831)
                ·
                  rfl

theorem cell19_269393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_269393 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269393 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269393 prefixEnd_269393 := by exact prefixLift 269393
  have htrace : WordTrace (prefixWord ++ tailWord_269393) baseStart_269393 baseEnd_269393 := by
    simpa [prefixWord, tailWord_269393, baseEnd_269393] using wordTrace_append hprefix tailTrace_269393
  have hstable : (prefixWord ++ tailWord_269393).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269393).length < 2 ^ (prefixWord ++ tailWord_269393).sum := by decide
  have hdescent : baseEnd_269393 < baseStart_269393 := by decide
  rcases family_descends (prefixWord ++ tailWord_269393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269410 : List Nat := [3, 3, 2, 2, 1, 8]
def baseStart_269410 : Nat := 118140960795 + 269410 * 2 ^ 59
def prefixEnd_269410 : Nat := 4983230072969 + 3 ^ 40 * 269410 * 2
def baseEnd_269410 : Nat := 9108597407598101454223

theorem tailTrace_269410 : CollatzResearch.WordTrace tailWord_269410 prefixEnd_269410 9108597407598101454223 := by
  unfold tailWord_269410
  simp only [CollatzResearch.WordTrace]
  refine ⟨2456547488495264102485421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6550793302654037606627789 2456547488495264102485421)
  ·
    refine ⟨921205308185724038432033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2456547488495264102485421 921205308185724038432033)
    ·
      refine ⟨690903981139293028824025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 921205308185724038432033 690903981139293028824025)
      ·
        refine ⟨518177985854469771618019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 690903981139293028824025 518177985854469771618019)
        ·
          refine ⟨777266978781704657427029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518177985854469771618019 777266978781704657427029)
          ·
            refine ⟨9108597407598101454223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 777266978781704657427029 9108597407598101454223)
            ·
              rfl

theorem cell19_269410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 8].length) (baseStart_269410 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269410 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269410 prefixEnd_269410 := by exact prefixLift 269410
  have htrace : WordTrace (prefixWord ++ tailWord_269410) baseStart_269410 baseEnd_269410 := by
    simpa [prefixWord, tailWord_269410, baseEnd_269410] using wordTrace_append hprefix tailTrace_269410
  have hstable : (prefixWord ++ tailWord_269410).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269410).length < 2 ^ (prefixWord ++ tailWord_269410).sum := by decide
  have hdescent : baseEnd_269410 < baseStart_269410 := by decide
  rcases family_descends (prefixWord ++ tailWord_269410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269469 : List Nat := [1, 4, 2, 1, 1, 2, 8]
def baseStart_269469 : Nat := 118140960795 + 269469 * 2 ^ 59
def prefixEnd_269469 : Nat := 4983230072969 + 3 ^ 40 * 269469 * 2
def baseEnd_269469 : Nat := 27331776491162752592245

theorem tailTrace_269469 : CollatzResearch.WordTrace tailWord_269469 prefixEnd_269469 27331776491162752592245 := by
  unfold tailWord_269469
  simp only [CollatzResearch.WordTrace]
  refine ⟨9828341860767309486339461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6552227907178206324226307 9828341860767309486339461)
  ·
    refine ⟨1842814098893870528688649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9828341860767309486339461 1842814098893870528688649)
    ·
      refine ⟨1382110574170402896516487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1842814098893870528688649 1382110574170402896516487)
      ·
        refine ⟨2073165861255604344774731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1382110574170402896516487 2073165861255604344774731)
        ·
          refine ⟨3109748791883406517162097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2073165861255604344774731 3109748791883406517162097)
          ·
            refine ⟨2332311593912554887871573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3109748791883406517162097 2332311593912554887871573)
            ·
              refine ⟨27331776491162752592245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2332311593912554887871573 27331776491162752592245)
              ·
                rfl

theorem cell19_269469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 8].length) (baseStart_269469 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269469 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269469 prefixEnd_269469 := by exact prefixLift 269469
  have htrace : WordTrace (prefixWord ++ tailWord_269469) baseStart_269469 baseEnd_269469 := by
    simpa [prefixWord, tailWord_269469, baseEnd_269469] using wordTrace_append hprefix tailTrace_269469
  have hstable : (prefixWord ++ tailWord_269469).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269469).length < 2 ^ (prefixWord ++ tailWord_269469).sum := by decide
  have hdescent : baseEnd_269469 < baseStart_269469 := by decide
  rcases family_descends (prefixWord ++ tailWord_269469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269619 : List Nat := [1, 1, 1, 2, 5, 3, 3, 3]
def baseStart_269619 : Nat := 118140960795 + 269619 * 2 ^ 59
def prefixEnd_269619 : Nat := 4983230072969 + 3 ^ 40 * 269619 * 2
def baseEnd_269619 : Nat := 82040972198332354442993

theorem tailTrace_269619 : CollatzResearch.WordTrace tailWord_269619 prefixEnd_269619 82040972198332354442993 := by
  unfold tailWord_269619
  simp only [CollatzResearch.WordTrace]
  refine ⟨9833812810223885104299911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6555875206815923402866607 9833812810223885104299911)
  ·
    refine ⟨14750719215335827656449867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9833812810223885104299911 14750719215335827656449867)
    ·
      refine ⟨22126078823003741484674801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14750719215335827656449867 22126078823003741484674801)
      ·
        refine ⟨16594559117252806113506101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22126078823003741484674801 16594559117252806113506101)
        ·
          refine ⟨1555739917242450573141197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16594559117252806113506101 1555739917242450573141197)
          ·
            refine ⟨583402468965918964927949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1555739917242450573141197 583402468965918964927949)
            ·
              refine ⟨218775925862219611847981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 583402468965918964927949 218775925862219611847981)
              ·
                refine ⟨82040972198332354442993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 218775925862219611847981 82040972198332354442993)
                ·
                  rfl

theorem cell19_269619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 3].length) (baseStart_269619 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269619 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269619 prefixEnd_269619 := by exact prefixLift 269619
  have htrace : WordTrace (prefixWord ++ tailWord_269619) baseStart_269619 baseEnd_269619 := by
    simpa [prefixWord, tailWord_269619, baseEnd_269619] using wordTrace_append hprefix tailTrace_269619
  have hstable : (prefixWord ++ tailWord_269619).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269619).length < 2 ^ (prefixWord ++ tailWord_269619).sum := by decide
  have hdescent : baseEnd_269619 < baseStart_269619 := by decide
  rcases family_descends (prefixWord ++ tailWord_269619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269672 : List Nat := [2, 1, 4, 2, 4, 1, 2, 3]
def baseStart_269672 : Nat := 118140960795 + 269672 * 2 ^ 59
def prefixEnd_269672 : Nat := 4983230072969 + 3 ^ 40 * 269672 * 2
def baseEnd_269672 : Nat := 82057099294443935265071

theorem tailTrace_269672 : CollatzResearch.WordTrace tailWord_269672 prefixEnd_269672 82057099294443935265071 := by
  unfold tailWord_269672
  simp only [CollatzResearch.WordTrace]
  refine ⟨4917872939515937577989635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6557163919354583437319513 4917872939515937577989635)
  ·
    refine ⟨7376809409273906366984453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4917872939515937577989635 7376809409273906366984453)
    ·
      refine ⟨1383151764238857443809585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7376809409273906366984453 1383151764238857443809585)
      ·
        refine ⟨1037363823179143082857189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1383151764238857443809585 1037363823179143082857189)
        ·
          refine ⟨194505716846089328035723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1037363823179143082857189 194505716846089328035723)
          ·
            refine ⟨291758575269133992053585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194505716846089328035723 291758575269133992053585)
            ·
              refine ⟨218818931451850494040189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291758575269133992053585 218818931451850494040189)
              ·
                refine ⟨82057099294443935265071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 218818931451850494040189 82057099294443935265071)
                ·
                  rfl

theorem cell19_269672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 3].length) (baseStart_269672 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269672 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269672 prefixEnd_269672 := by exact prefixLift 269672
  have htrace : WordTrace (prefixWord ++ tailWord_269672) baseStart_269672 baseEnd_269672 := by
    simpa [prefixWord, tailWord_269672, baseEnd_269672] using wordTrace_append hprefix tailTrace_269672
  have hstable : (prefixWord ++ tailWord_269672).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269672).length < 2 ^ (prefixWord ++ tailWord_269672).sum := by decide
  have hdescent : baseEnd_269672 < baseStart_269672 := by decide
  rcases family_descends (prefixWord ++ tailWord_269672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269676 : List Nat := [2, 2, 1, 1, 5, 1, 4, 3]
def baseStart_269676 : Nat := 118140960795 + 269676 * 2 ^ 59
def prefixEnd_269676 : Nat := 4983230072969 + 3 ^ 40 * 269676 * 2
def baseEnd_269676 : Nat := 82058316433773111176171

theorem tailTrace_269676 : CollatzResearch.WordTrace tailWord_269676 prefixEnd_269676 82058316433773111176171 := by
  unfold tailWord_269676
  simp only [CollatzResearch.WordTrace]
  refine ⟨4917945885508691919562441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6557261180678255892749921 4917945885508691919562441)
  ·
    refine ⟨3688459414131518939671831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4917945885508691919562441 3688459414131518939671831)
    ·
      refine ⟨5532689121197278409507747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3688459414131518939671831 5532689121197278409507747)
      ·
        refine ⟨8299033681795917614261621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5532689121197278409507747 8299033681795917614261621)
        ·
          refine ⟨778034407668367276337027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8299033681795917614261621 778034407668367276337027)
          ·
            refine ⟨1167051611502550914505541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778034407668367276337027 1167051611502550914505541)
            ·
              refine ⟨218822177156728296469789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1167051611502550914505541 218822177156728296469789)
              ·
                refine ⟨82058316433773111176171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 218822177156728296469789 82058316433773111176171)
                ·
                  rfl

theorem cell19_269676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_269676 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269676 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269676 prefixEnd_269676 := by exact prefixLift 269676
  have htrace : WordTrace (prefixWord ++ tailWord_269676) baseStart_269676 baseEnd_269676 := by
    simpa [prefixWord, tailWord_269676, baseEnd_269676] using wordTrace_append hprefix tailTrace_269676
  have hstable : (prefixWord ++ tailWord_269676).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269676).length < 2 ^ (prefixWord ++ tailWord_269676).sum := by decide
  have hdescent : baseEnd_269676 < baseStart_269676 := by decide
  rcases family_descends (prefixWord ++ tailWord_269676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269735 : List Nat := [1, 1, 6, 1, 1, 1, 1, 7]
def baseStart_269735 : Nat := 118140960795 + 269735 * 2 ^ 59
def prefixEnd_269735 : Nat := 4983230072969 + 3 ^ 40 * 269735 * 2
def baseEnd_269735 : Nat := 82076269238878455864899

theorem tailTrace_269735 : CollatzResearch.WordTrace tailWord_269735 prefixEnd_269735 82076269238878455864899 := by
  unfold tailWord_269735
  simp only [CollatzResearch.WordTrace]
  refine ⟨9838043677803636915522659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6558695785202424610348439 9838043677803636915522659)
  ·
    refine ⟨14757065516705455373283989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9838043677803636915522659 14757065516705455373283989)
    ·
      refine ⟨691737446095568220622687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14757065516705455373283989 691737446095568220622687)
      ·
        refine ⟨1037606169143352330934031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 691737446095568220622687 1037606169143352330934031)
        ·
          refine ⟨1556409253715028496401047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1037606169143352330934031 1556409253715028496401047)
          ·
            refine ⟨2334613880572542744601571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1556409253715028496401047 2334613880572542744601571)
            ·
              refine ⟨3501920820858814116902357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2334613880572542744601571 3501920820858814116902357)
              ·
                refine ⟨82076269238878455864899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3501920820858814116902357 82076269238878455864899)
                ·
                  rfl

theorem cell19_269735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_269735 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269735 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269735 prefixEnd_269735 := by exact prefixLift 269735
  have htrace : WordTrace (prefixWord ++ tailWord_269735) baseStart_269735 baseEnd_269735 := by
    simpa [prefixWord, tailWord_269735, baseEnd_269735] using wordTrace_append hprefix tailTrace_269735
  have hstable : (prefixWord ++ tailWord_269735).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269735).length < 2 ^ (prefixWord ++ tailWord_269735).sum := by decide
  have hdescent : baseEnd_269735 < baseStart_269735 := by decide
  rcases family_descends (prefixWord ++ tailWord_269735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269864 : List Nat := [2, 1, 5, 2, 3, 1, 5]
def baseStart_269864 : Nat := 118140960795 + 269864 * 2 ^ 59
def prefixEnd_269864 : Nat := 4983230072969 + 3 ^ 40 * 269864 * 2
def baseEnd_269864 : Nat := 27371840660748126332627

theorem tailTrace_269864 : CollatzResearch.WordTrace tailWord_269864 prefixEnd_269864 27371840660748126332627 := by
  unfold tailWord_269864
  simp only [CollatzResearch.WordTrace]
  refine ⟨4921374347168145973484323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6561832462890861297979097 4921374347168145973484323)
  ·
    refine ⟨7382061520752218960226485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4921374347168145973484323 7382061520752218960226485)
    ·
      refine ⟨692068267570520527521233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7382061520752218960226485 692068267570520527521233)
      ·
        refine ⟨519051200677890395640925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 692068267570520527521233 519051200677890395640925)
        ·
          refine ⟨194644200254208898365347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 519051200677890395640925 194644200254208898365347)
          ·
            refine ⟨291966300381313347548021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194644200254208898365347 291966300381313347548021)
            ·
              refine ⟨27371840660748126332627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 291966300381313347548021 27371840660748126332627)
              ·
                rfl

theorem cell19_269864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 5].length) (baseStart_269864 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269864 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269864 prefixEnd_269864 := by exact prefixLift 269864
  have htrace : WordTrace (prefixWord ++ tailWord_269864) baseStart_269864 baseEnd_269864 := by
    simpa [prefixWord, tailWord_269864, baseEnd_269864] using wordTrace_append hprefix tailTrace_269864
  have hstable : (prefixWord ++ tailWord_269864).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269864).length < 2 ^ (prefixWord ++ tailWord_269864).sum := by decide
  have hdescent : baseEnd_269864 < baseStart_269864 := by decide
  rcases family_descends (prefixWord ++ tailWord_269864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269885 : List Nat := [1, 4, 1, 3, 3, 1, 2, 4]
def baseStart_269885 : Nat := 118140960795 + 269885 * 2 ^ 59
def prefixEnd_269885 : Nat := 4983230072969 + 3 ^ 40 * 269885 * 2
def baseEnd_269885 : Nat := 82121911963722552531157

theorem tailTrace_269885 : CollatzResearch.WordTrace tailWord_269885 prefixEnd_269885 82121911963722552531157 := by
  unfold tailWord_269885
  simp only [CollatzResearch.WordTrace]
  refine ⟨9843514627260212533483109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6562343084840141688988739 9843514627260212533483109)
  ·
    refine ⟨1845658992611289850028083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9843514627260212533483109 1845658992611289850028083)
    ·
      refine ⟨2768488488916934775042125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1845658992611289850028083 2768488488916934775042125)
      ·
        refine ⟨1038183183343850540640797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2768488488916934775042125 1038183183343850540640797)
        ·
          refine ⟨389318693753943952740299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1038183183343850540640797 389318693753943952740299)
          ·
            refine ⟨583978040630915929110449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389318693753943952740299 583978040630915929110449)
            ·
              refine ⟨437983530473186946832837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 583978040630915929110449 437983530473186946832837)
              ·
                refine ⟨82121911963722552531157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 437983530473186946832837 82121911963722552531157)
                ·
                  rfl

theorem cell19_269885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 4].length) (baseStart_269885 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269885 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269885 prefixEnd_269885 := by exact prefixLift 269885
  have htrace : WordTrace (prefixWord ++ tailWord_269885) baseStart_269885 baseEnd_269885 := by
    simpa [prefixWord, tailWord_269885, baseEnd_269885] using wordTrace_append hprefix tailTrace_269885
  have hstable : (prefixWord ++ tailWord_269885).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269885).length < 2 ^ (prefixWord ++ tailWord_269885).sum := by decide
  have hdescent : baseEnd_269885 < baseStart_269885 := by decide
  rcases family_descends (prefixWord ++ tailWord_269885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269887 : List Nat := [1, 1, 2, 2, 3, 4, 2, 4]
def baseStart_269887 : Nat := 118140960795 + 269887 * 2 ^ 59
def prefixEnd_269887 : Nat := 4983230072969 + 3 ^ 40 * 269887 * 2
def baseEnd_269887 : Nat := 82122520533387140486707

theorem tailTrace_269887 : CollatzResearch.WordTrace tailWord_269887 prefixEnd_269887 82122520533387140486707 := by
  unfold tailWord_269887
  simp only [CollatzResearch.WordTrace]
  refine ⟨9843587573252966875055915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6562391715501977916703943 9843587573252966875055915)
  ·
    refine ⟨14765381359879450312583873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9843587573252966875055915 14765381359879450312583873)
    ·
      refine ⟨11074036019909587734437905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14765381359879450312583873 11074036019909587734437905)
      ·
        refine ⟨8305527014932190800828429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11074036019909587734437905 8305527014932190800828429)
        ·
          refine ⟨3114572630599571550310661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8305527014932190800828429 3114572630599571550310661)
          ·
            refine ⟨583982368237419665683249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3114572630599571550310661 583982368237419665683249)
            ·
              refine ⟨437986776178064749262437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 583982368237419665683249 437986776178064749262437)
              ·
                refine ⟨82122520533387140486707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 437986776178064749262437 82122520533387140486707)
                ·
                  rfl

theorem cell19_269887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_269887 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269887 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269887 prefixEnd_269887 := by exact prefixLift 269887
  have htrace : WordTrace (prefixWord ++ tailWord_269887) baseStart_269887 baseEnd_269887 := by
    simpa [prefixWord, tailWord_269887, baseEnd_269887] using wordTrace_append hprefix tailTrace_269887
  have hstable : (prefixWord ++ tailWord_269887).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269887).length < 2 ^ (prefixWord ++ tailWord_269887).sum := by decide
  have hdescent : baseEnd_269887 < baseStart_269887 := by decide
  rcases family_descends (prefixWord ++ tailWord_269887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269906 : List Nat := [3, 2, 2, 1, 2, 2, 2, 5]
def baseStart_269906 : Nat := 118140960795 + 269906 * 2 ^ 59
def prefixEnd_269906 : Nat := 4983230072969 + 3 ^ 40 * 269906 * 2
def baseEnd_269906 : Nat := 82128301945200726064433

theorem tailTrace_269906 : CollatzResearch.WordTrace tailWord_269906 prefixEnd_269906 82128301945200726064433 := by
  unfold tailWord_269906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2461070140046033279999393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6562853706789422079998381 2461070140046033279999393)
  ·
    refine ⟨1845802605034524959999545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2461070140046033279999393 1845802605034524959999545)
    ·
      refine ⟨1384351953775893719999659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1845802605034524959999545 1384351953775893719999659)
      ·
        refine ⟨2076527930663840579999489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1384351953775893719999659 2076527930663840579999489)
        ·
          refine ⟨1557395947997880434999617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2076527930663840579999489 1557395947997880434999617)
          ·
            refine ⟨1168046960998410326249713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1557395947997880434999617 1168046960998410326249713)
            ·
              refine ⟨876035220748807744687285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1168046960998410326249713 876035220748807744687285)
              ·
                refine ⟨82128301945200726064433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 876035220748807744687285 82128301945200726064433)
                ·
                  rfl

theorem cell19_269906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_269906 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269906 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269906 prefixEnd_269906 := by exact prefixLift 269906
  have htrace : WordTrace (prefixWord ++ tailWord_269906) baseStart_269906 baseEnd_269906 := by
    simpa [prefixWord, tailWord_269906, baseEnd_269906] using wordTrace_append hprefix tailTrace_269906
  have hstable : (prefixWord ++ tailWord_269906).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269906).length < 2 ^ (prefixWord ++ tailWord_269906).sum := by decide
  have hdescent : baseEnd_269906 < baseStart_269906 := by decide
  rcases family_descends (prefixWord ++ tailWord_269906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269942 : List Nat := [5, 1, 1, 2, 2, 1, 3, 4]
def baseStart_269942 : Nat := 118140960795 + 269942 * 2 ^ 59
def prefixEnd_269942 : Nat := 4983230072969 + 3 ^ 40 * 269942 * 2
def baseEnd_269942 : Nat := 82139256199163309264335

theorem tailTrace_269942 : CollatzResearch.WordTrace tailWord_269942 prefixEnd_269942 82139256199163309264335 := by
  unfold tailWord_269942
  simp only [CollatzResearch.WordTrace]
  refine ⟨615349599253356954269255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6563729058702474178872053 615349599253356954269255)
  ·
    refine ⟨923024398880035431403883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 615349599253356954269255 923024398880035431403883)
    ·
      refine ⟨1384536598320053147105825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 923024398880035431403883 1384536598320053147105825)
      ·
        refine ⟨1038402448740039860329369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1384536598320053147105825 1038402448740039860329369)
        ·
          refine ⟨778801836555029895247027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1038402448740039860329369 778801836555029895247027)
          ·
            refine ⟨1168202754832544842870541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778801836555029895247027 1168202754832544842870541)
            ·
              refine ⟨438076033062204316076453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1168202754832544842870541 438076033062204316076453)
              ·
                refine ⟨82139256199163309264335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 438076033062204316076453 82139256199163309264335)
                ·
                  rfl

theorem cell19_269942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_269942 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_269942 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_269942 prefixEnd_269942 := by exact prefixLift 269942
  have htrace : WordTrace (prefixWord ++ tailWord_269942) baseStart_269942 baseEnd_269942 := by
    simpa [prefixWord, tailWord_269942, baseEnd_269942] using wordTrace_append hprefix tailTrace_269942
  have hstable : (prefixWord ++ tailWord_269942).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269942).length < 2 ^ (prefixWord ++ tailWord_269942).sum := by decide
  have hdescent : baseEnd_269942 < baseStart_269942 := by decide
  rcases family_descends (prefixWord ++ tailWord_269942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
