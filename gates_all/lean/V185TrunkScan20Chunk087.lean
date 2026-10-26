import V185TrunkScan20Chunk086

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_529586 : List Nat := [3, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_529586 : Nat := 118140960795 + 529586 * 2 ^ 59
def prefixEnd_529586 : Nat := 4983230072969 + 3 ^ 40 * 529586 * 2
def baseEnd_529586 : Nat := 241717480792951312035097

theorem tailTrace_529586 : CollatzResearch.WordTrace tailWord_529586 prefixEnd_529586 241717480792951312035097 := by
  unfold tailWord_529586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4828897064851960733282153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12877058839605228622085741 4828897064851960733282153)
  ·
    refine ⟨3621672798638970549961615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4828897064851960733282153 3621672798638970549961615)
    ·
      refine ⟨5432509197958455824942423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3621672798638970549961615 5432509197958455824942423)
      ·
        refine ⟨8148763796937683737413635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5432509197958455824942423 8148763796937683737413635)
        ·
          refine ⟨12223145695406525606120453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8148763796937683737413635 12223145695406525606120453)
          ·
            refine ⟨2291839817888723551147585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12223145695406525606120453 2291839817888723551147585)
            ·
              refine ⟨1718879863416542663360689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2291839817888723551147585 1718879863416542663360689)
              ·
                refine ⟨1289159897562406997520517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1718879863416542663360689 1289159897562406997520517)
                ·
                  refine ⟨241717480792951312035097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1289159897562406997520517 241717480792951312035097)
                  ·
                    rfl

theorem cell20_529586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_529586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529586 prefixEnd_529586 := by exact prefixLift 529586
  have htrace : WordTrace (prefixWord ++ tailWord_529586) baseStart_529586 baseEnd_529586 := by
    simpa [prefixWord, tailWord_529586, baseEnd_529586] using wordTrace_append hprefix tailTrace_529586
  have hstable : (prefixWord ++ tailWord_529586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529586).length < 2 ^ (prefixWord ++ tailWord_529586).sum := by decide
  have hdescent : baseEnd_529586 < baseStart_529586 := by decide
  rcases family_descends (prefixWord ++ tailWord_529586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529593 : List Nat := [1, 2, 1, 4, 1, 4, 1, 6]
def baseStart_529593 : Nat := 118140960795 + 529593 * 2 ^ 59
def prefixEnd_529593 : Nat := 4983230072969 + 3 ^ 40 * 529593 * 2
def baseEnd_529593 : Nat := 80573558594563466267245

theorem tailTrace_529593 : CollatzResearch.WordTrace tailWord_529593 prefixEnd_529593 80573558594563466267245 := by
  unfold tailWord_529593
  simp only [CollatzResearch.WordTrace]
  refine ⟨19315843570382483128633433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12877229046921655419088955 19315843570382483128633433)
  ·
    refine ⟨14486882677786862346475075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19315843570382483128633433 14486882677786862346475075)
    ·
      refine ⟨21730324016680293519712613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14486882677786862346475075 21730324016680293519712613)
      ·
        refine ⟨4074435753127555034946115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21730324016680293519712613 4074435753127555034946115)
        ·
          refine ⟨6111653629691332552419173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4074435753127555034946115 6111653629691332552419173)
          ·
            refine ⟨1145935055567124853578595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6111653629691332552419173 1145935055567124853578595)
            ·
              refine ⟨1718902583350687280367893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145935055567124853578595 1718902583350687280367893)
              ·
                refine ⟨80573558594563466267245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1718902583350687280367893 80573558594563466267245)
                ·
                  rfl

theorem cell20_529593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 6].length) (baseStart_529593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529593 prefixEnd_529593 := by exact prefixLift 529593
  have htrace : WordTrace (prefixWord ++ tailWord_529593) baseStart_529593 baseEnd_529593 := by
    simpa [prefixWord, tailWord_529593, baseEnd_529593] using wordTrace_append hprefix tailTrace_529593
  have hstable : (prefixWord ++ tailWord_529593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529593).length < 2 ^ (prefixWord ++ tailWord_529593).sum := by decide
  have hdescent : baseEnd_529593 < baseStart_529593 := by decide
  rcases family_descends (prefixWord ++ tailWord_529593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529607 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 6]
def baseStart_529607 : Nat := 118140960795 + 529607 * 2 ^ 59
def prefixEnd_529607 : Nat := 4983230072969 + 3 ^ 40 * 529607 * 2
def baseEnd_529607 : Nat := 241727065765168572335011

theorem tailTrace_529607 : CollatzResearch.WordTrace tailWord_529607 prefixEnd_529607 241727065765168572335011 := by
  unfold tailWord_529607
  simp only [CollatzResearch.WordTrace]
  refine ⟨19316354192331763519643075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12877569461554509013095383 19316354192331763519643075)
  ·
    refine ⟨28974531288497645279464613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19316354192331763519643075 28974531288497645279464613)
    ·
      refine ⟨5432724616593308489899615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28974531288497645279464613 5432724616593308489899615)
      ·
        refine ⟨8149086924889962734849423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5432724616593308489899615 8149086924889962734849423)
        ·
          refine ⟨12223630387334944102274135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8149086924889962734849423 12223630387334944102274135)
          ·
            refine ⟨18335445581002416153411203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12223630387334944102274135 18335445581002416153411203)
            ·
              refine ⟨27503168371503624230116805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18335445581002416153411203 27503168371503624230116805)
              ·
                refine ⟨5156844069656929543146901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27503168371503624230116805 5156844069656929543146901)
                ·
                  refine ⟨241727065765168572335011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5156844069656929543146901 241727065765168572335011)
                  ·
                    rfl

theorem cell20_529607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_529607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529607 prefixEnd_529607 := by exact prefixLift 529607
  have htrace : WordTrace (prefixWord ++ tailWord_529607) baseStart_529607 baseEnd_529607 := by
    simpa [prefixWord, tailWord_529607, baseEnd_529607] using wordTrace_append hprefix tailTrace_529607
  have hstable : (prefixWord ++ tailWord_529607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529607).length < 2 ^ (prefixWord ++ tailWord_529607).sum := by decide
  have hdescent : baseEnd_529607 < baseStart_529607 := by decide
  rcases family_descends (prefixWord ++ tailWord_529607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529672 : List Nat := [2, 1, 3, 2, 4, 1, 2, 2, 3]
def baseStart_529672 : Nat := 118140960795 + 529672 * 2 ^ 59
def prefixEnd_529672 : Nat := 4983230072969 + 3 ^ 40 * 529672 * 2
def baseEnd_529672 : Nat := 241756733536317235168079

theorem tailTrace_529672 : CollatzResearch.WordTrace tailWord_529672 prefixEnd_529672 241756733536317235168079 := by
  unfold tailWord_529672
  simp only [CollatzResearch.WordTrace]
  refine ⟨9659362468548139810379635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12879149958064186413839513 9659362468548139810379635)
  ·
    refine ⟨14489043702822209715569453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9659362468548139810379635 14489043702822209715569453)
    ·
      refine ⟨5433391388558328643338545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14489043702822209715569453 5433391388558328643338545)
      ·
        refine ⟨4075043541418746482503909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5433391388558328643338545 4075043541418746482503909)
        ·
          refine ⟨764070664016014965469483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4075043541418746482503909 764070664016014965469483)
          ·
            refine ⟨1146105996024022448204225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764070664016014965469483 1146105996024022448204225)
            ·
              refine ⟨859579497018016836153169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1146105996024022448204225 859579497018016836153169)
              ·
                refine ⟨644684622763512627114877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 859579497018016836153169 644684622763512627114877)
                ·
                  refine ⟨241756733536317235168079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644684622763512627114877 241756733536317235168079)
                  ·
                    rfl

theorem cell20_529672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_529672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529672 prefixEnd_529672 := by exact prefixLift 529672
  have htrace : WordTrace (prefixWord ++ tailWord_529672) baseStart_529672 baseEnd_529672 := by
    simpa [prefixWord, tailWord_529672, baseEnd_529672] using wordTrace_append hprefix tailTrace_529672
  have hstable : (prefixWord ++ tailWord_529672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529672).length < 2 ^ (prefixWord ++ tailWord_529672).sum := by decide
  have hdescent : baseEnd_529672 < baseStart_529672 := by decide
  rcases family_descends (prefixWord ++ tailWord_529672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529682 : List Nat := [3, 2, 4, 2, 1, 2, 1, 5]
def baseStart_529682 : Nat := 118140960795 + 529682 * 2 ^ 59
def prefixEnd_529682 : Nat := 4983230072969 + 3 ^ 40 * 529682 * 2
def baseEnd_529682 : Nat := 80587099269600548278235

theorem tailTrace_529682 : CollatzResearch.WordTrace tailWord_529682 prefixEnd_529682 80587099269600548278235 := by
  unfold tailWord_529682
  simp only [CollatzResearch.WordTrace]
  refine ⟨4829772416765012832155825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12879393111373367552415533 4829772416765012832155825)
  ·
    refine ⟨3622329312573759624116869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4829772416765012832155825 3622329312573759624116869)
    ·
      refine ⟨679186746107579929521913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3622329312573759624116869 679186746107579929521913)
      ·
        refine ⟨509390059580684947141435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679186746107579929521913 509390059580684947141435)
        ·
          refine ⟨764085089371027420712153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509390059580684947141435 764085089371027420712153)
          ·
            refine ⟨573063817028270565534115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764085089371027420712153 573063817028270565534115)
            ·
              refine ⟨859595725542405848301173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573063817028270565534115 859595725542405848301173)
              ·
                refine ⟨80587099269600548278235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 859595725542405848301173 80587099269600548278235)
                ·
                  rfl

theorem cell20_529682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_529682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529682 prefixEnd_529682 := by exact prefixLift 529682
  have htrace : WordTrace (prefixWord ++ tailWord_529682) baseStart_529682 baseEnd_529682 := by
    simpa [prefixWord, tailWord_529682, baseEnd_529682] using wordTrace_append hprefix tailTrace_529682
  have hstable : (prefixWord ++ tailWord_529682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529682).length < 2 ^ (prefixWord ++ tailWord_529682).sum := by decide
  have hdescent : baseEnd_529682 < baseStart_529682 := by decide
  rcases family_descends (prefixWord ++ tailWord_529682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529700 : List Nat := [2, 3, 1, 3, 1, 1, 3, 2, 4]
def baseStart_529700 : Nat := 118140960795 + 529700 * 2 ^ 59
def prefixEnd_529700 : Nat := 4983230072969 + 3 ^ 40 * 529700 * 2
def baseEnd_529700 : Nat := 241769513499273582234631

theorem tailTrace_529700 : CollatzResearch.WordTrace tailWord_529700 prefixEnd_529700 241769513499273582234631 := by
  unfold tailWord_529700
  simp only [CollatzResearch.WordTrace]
  refine ⟨9659873090497420201389277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12879830787329893601852369 9659873090497420201389277)
  ·
    refine ⟨3622452408936532575520979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9659873090497420201389277 3622452408936532575520979)
    ·
      refine ⟨5433678613404798863281469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3622452408936532575520979 5433678613404798863281469)
      ·
        refine ⟨2037629480026799573730551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5433678613404798863281469 2037629480026799573730551)
        ·
          refine ⟨3056444220040199360595827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2037629480026799573730551 3056444220040199360595827)
          ·
            refine ⟨4584666330060299040893741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3056444220040199360595827 4584666330060299040893741)
            ·
              refine ⟨1719249873772612140335153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4584666330060299040893741 1719249873772612140335153)
              ·
                refine ⟨1289437405329459105251365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1719249873772612140335153 1289437405329459105251365)
                ·
                  refine ⟨241769513499273582234631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1289437405329459105251365 241769513499273582234631)
                  ·
                    rfl

theorem cell20_529700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_529700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529700 prefixEnd_529700 := by exact prefixLift 529700
  have htrace : WordTrace (prefixWord ++ tailWord_529700) baseStart_529700 baseEnd_529700 := by
    simpa [prefixWord, tailWord_529700, baseEnd_529700] using wordTrace_append hprefix tailTrace_529700
  have hstable : (prefixWord ++ tailWord_529700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529700).length < 2 ^ (prefixWord ++ tailWord_529700).sum := by decide
  have hdescent : baseEnd_529700 < baseStart_529700 := by decide
  rcases family_descends (prefixWord ++ tailWord_529700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529717 : List Nat := [1, 3, 3, 1, 2, 2, 1, 5, 2]
def baseStart_529717 : Nat := 118140960795 + 529717 * 2 ^ 59
def prefixEnd_529717 : Nat := 4983230072969 + 3 ^ 40 * 529717 * 2
def baseEnd_529717 : Nat := 241777272762497078667895

theorem tailTrace_529717 : CollatzResearch.WordTrace tailWord_529717 prefixEnd_529717 241777272762497078667895 := by
  unfold tailWord_529717
  simp only [CollatzResearch.WordTrace]
  refine ⟨19320366221933252306147405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12880244147955501537431603 19320366221933252306147405)
  ·
    refine ⟨7245137333224969614805277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19320366221933252306147405 7245137333224969614805277)
    ·
      refine ⟨2716926499959363605551979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7245137333224969614805277 2716926499959363605551979)
      ·
        refine ⟨4075389749939045408327969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2716926499959363605551979 4075389749939045408327969)
        ·
          refine ⟨3056542312454284056245977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4075389749939045408327969 3056542312454284056245977)
          ·
            refine ⟨2292406734340713042184483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3056542312454284056245977 2292406734340713042184483)
            ·
              refine ⟨3438610101511069563276725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2292406734340713042184483 3438610101511069563276725)
              ·
                refine ⟨322369697016662771557193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3438610101511069563276725 322369697016662771557193)
                ·
                  refine ⟨241777272762497078667895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322369697016662771557193 241777272762497078667895)
                  ·
                    rfl

theorem cell20_529717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_529717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529717 prefixEnd_529717 := by exact prefixLift 529717
  have htrace : WordTrace (prefixWord ++ tailWord_529717) baseStart_529717 baseEnd_529717 := by
    simpa [prefixWord, tailWord_529717, baseEnd_529717] using wordTrace_append hprefix tailTrace_529717
  have hstable : (prefixWord ++ tailWord_529717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529717).length < 2 ^ (prefixWord ++ tailWord_529717).sum := by decide
  have hdescent : baseEnd_529717 < baseStart_529717 := by decide
  rcases family_descends (prefixWord ++ tailWord_529717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529728 : List Nat := [2, 1, 1, 2, 2, 1, 11]
def baseStart_529728 : Nat := 118140960795 + 529728 * 2 ^ 59
def prefixEnd_529728 : Nat := 4983230072969 + 3 ^ 40 * 529728 * 2
def baseEnd_529728 : Nat := 26864699273581103255687

theorem tailTrace_529728 : CollatzResearch.WordTrace tailWord_529728 prefixEnd_529728 26864699273581103255687 := by
  unfold tailWord_529728
  simp only [CollatzResearch.WordTrace]
  refine ⟨9660383712446700592398919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12880511616595600789865225 9660383712446700592398919)
  ·
    refine ⟨14490575568670050888598379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9660383712446700592398919 14490575568670050888598379)
    ·
      refine ⟨21735863353005076332897569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14490575568670050888598379 21735863353005076332897569)
      ·
        refine ⟨16301897514753807249673177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21735863353005076332897569 16301897514753807249673177)
        ·
          refine ⟨12226423136065355437254883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16301897514753807249673177 12226423136065355437254883)
          ·
            refine ⟨18339634704098033155882325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12226423136065355437254883 18339634704098033155882325)
            ·
              refine ⟨26864699273581103255687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18339634704098033155882325 26864699273581103255687)
              ·
                rfl

theorem cell20_529728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 11].length) (baseStart_529728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529728 prefixEnd_529728 := by exact prefixLift 529728
  have htrace : WordTrace (prefixWord ++ tailWord_529728) baseStart_529728 baseEnd_529728 := by
    simpa [prefixWord, tailWord_529728, baseEnd_529728] using wordTrace_append hprefix tailTrace_529728
  have hstable : (prefixWord ++ tailWord_529728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529728).length < 2 ^ (prefixWord ++ tailWord_529728).sum := by decide
  have hdescent : baseEnd_529728 < baseStart_529728 := by decide
  rcases family_descends (prefixWord ++ tailWord_529728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529748 : List Nat := [2, 4, 1, 1, 2, 1, 5, 1, 3]
def baseStart_529748 : Nat := 118140960795 + 529748 * 2 ^ 59
def prefixEnd_529748 : Nat := 4983230072969 + 3 ^ 40 * 529748 * 2
def baseEnd_529748 : Nat := 241791422007198748634435

theorem tailTrace_529748 : CollatzResearch.WordTrace tailWord_529748 prefixEnd_529748 241791422007198748634435 := by
  unfold tailWord_529748
  simp only [CollatzResearch.WordTrace]
  refine ⟨9660748442410472300262949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12880997923213963067017265 9660748442410472300262949)
  ·
    refine ⟨1811390332951963556299303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9660748442410472300262949 1811390332951963556299303)
    ·
      refine ⟨2717085499427945334448955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1811390332951963556299303 2717085499427945334448955)
      ·
        refine ⟨4075628249141918001673433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2717085499427945334448955 4075628249141918001673433)
        ·
          refine ⟨3056721186856438501255075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4075628249141918001673433 3056721186856438501255075)
          ·
            refine ⟨4585081780284657751882613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3056721186856438501255075 4585081780284657751882613)
            ·
              refine ⟨429851416901686664238995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4585081780284657751882613 429851416901686664238995)
              ·
                refine ⟨644777125352529996358493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429851416901686664238995 644777125352529996358493)
                ·
                  refine ⟨241791422007198748634435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644777125352529996358493 241791422007198748634435)
                  ·
                    rfl

theorem cell20_529748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_529748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529748 prefixEnd_529748 := by exact prefixLift 529748
  have htrace : WordTrace (prefixWord ++ tailWord_529748) baseStart_529748 baseEnd_529748 := by
    simpa [prefixWord, tailWord_529748, baseEnd_529748] using wordTrace_append hprefix tailTrace_529748
  have hstable : (prefixWord ++ tailWord_529748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529748).length < 2 ^ (prefixWord ++ tailWord_529748).sum := by decide
  have hdescent : baseEnd_529748 < baseStart_529748 := by decide
  rcases family_descends (prefixWord ++ tailWord_529748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529772 : List Nat := [2, 2, 1, 1, 5, 3, 1, 3, 2]
def baseStart_529772 : Nat := 118140960795 + 529772 * 2 ^ 59
def prefixEnd_529772 : Nat := 4983230072969 + 3 ^ 40 * 529772 * 2
def baseEnd_529772 : Nat := 241802376261161331834337

theorem tailTrace_529772 : CollatzResearch.WordTrace tailWord_529772 prefixEnd_529772 241802376261161331834337 := by
  unfold tailWord_529772
  simp only [CollatzResearch.WordTrace]
  refine ⟨9661186118366998349699785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12881581491155997799599713 9661186118366998349699785)
  ·
    refine ⟨7245889588775248762274839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9661186118366998349699785 7245889588775248762274839)
    ·
      refine ⟨10868834383162873143412259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7245889588775248762274839 10868834383162873143412259)
      ·
        refine ⟨16303251574744309715118389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10868834383162873143412259 16303251574744309715118389)
        ·
          refine ⟨1528429835132279035792349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16303251574744309715118389 1528429835132279035792349)
          ·
            refine ⟨573161188174604638422131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1528429835132279035792349 573161188174604638422131)
            ·
              refine ⟨859741782261906957633197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573161188174604638422131 859741782261906957633197)
              ·
                refine ⟨322403168348215109112449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 859741782261906957633197 322403168348215109112449)
                ·
                  refine ⟨241802376261161331834337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322403168348215109112449 241802376261161331834337)
                  ·
                    rfl

theorem cell20_529772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_529772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529772 prefixEnd_529772 := by exact prefixLift 529772
  have htrace : WordTrace (prefixWord ++ tailWord_529772) baseStart_529772 baseEnd_529772 := by
    simpa [prefixWord, tailWord_529772, baseEnd_529772] using wordTrace_append hprefix tailTrace_529772
  have hstable : (prefixWord ++ tailWord_529772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529772).length < 2 ^ (prefixWord ++ tailWord_529772).sum := by decide
  have hdescent : baseEnd_529772 < baseStart_529772 := by decide
  rcases family_descends (prefixWord ++ tailWord_529772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529821 : List Nat := [1, 4, 2, 1, 3, 1, 2, 6]
def baseStart_529821 : Nat := 118140960795 + 529821 * 2 ^ 59
def prefixEnd_529821 : Nat := 4983230072969 + 3 ^ 40 * 529821 * 2
def baseEnd_529821 : Nat := 80608247065444979733601

theorem tailTrace_529821 : CollatzResearch.WordTrace tailWord_529821 prefixEnd_529821 80608247065444979733601 := by
  unfold tailWord_529821
  simp only [CollatzResearch.WordTrace]
  refine ⟨19324159413556478067933317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12882772942370985378622211 19324159413556478067933317)
  ·
    refine ⟨3623279890041839637737497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19324159413556478067933317 3623279890041839637737497)
    ·
      refine ⟨2717459917531379728303123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3623279890041839637737497 2717459917531379728303123)
      ·
        refine ⟨4076189876297069592454685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2717459917531379728303123 4076189876297069592454685)
        ·
          refine ⟨1528571203611401097170507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4076189876297069592454685 1528571203611401097170507)
          ·
            refine ⟨2292856805417101645755761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1528571203611401097170507 2292856805417101645755761)
            ·
              refine ⟨1719642604062826234316821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2292856805417101645755761 1719642604062826234316821)
              ·
                refine ⟨80608247065444979733601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1719642604062826234316821 80608247065444979733601)
                ·
                  rfl

theorem cell20_529821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 6].length) (baseStart_529821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529821 prefixEnd_529821 := by exact prefixLift 529821
  have htrace : WordTrace (prefixWord ++ tailWord_529821) baseStart_529821 baseEnd_529821 := by
    simpa [prefixWord, tailWord_529821, baseEnd_529821] using wordTrace_append hprefix tailTrace_529821
  have hstable : (prefixWord ++ tailWord_529821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529821).length < 2 ^ (prefixWord ++ tailWord_529821).sum := by decide
  have hdescent : baseEnd_529821 < baseStart_529821 := by decide
  rcases family_descends (prefixWord ++ tailWord_529821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529831 : List Nat := [1, 1, 6, 1, 1, 1, 2, 5, 2]
def baseStart_529831 : Nat := 118140960795 + 529831 * 2 ^ 59
def prefixEnd_529831 : Nat := 4983230072969 + 3 ^ 40 * 529831 * 2
def baseEnd_529831 : Nat := 241829305468819348867429

theorem tailTrace_529831 : CollatzResearch.WordTrace tailWord_529831 prefixEnd_529831 241829305468819348867429 := by
  unfold tailWord_529831
  simp only [CollatzResearch.WordTrace]
  refine ⟨19324524143520249775797347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12883016095680166517198231 19324524143520249775797347)
  ·
    refine ⟨28986786215280374663696021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19324524143520249775797347 28986786215280374663696021)
    ·
      refine ⟨1358755603841267562360751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28986786215280374663696021 1358755603841267562360751)
      ·
        refine ⟨2038133405761901343541127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1358755603841267562360751 2038133405761901343541127)
        ·
          refine ⟨3057200108642852015311691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2038133405761901343541127 3057200108642852015311691)
          ·
            refine ⟨4585800162964278022967537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3057200108642852015311691 4585800162964278022967537)
            ·
              refine ⟨3439350122223208517225653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4585800162964278022967537 3439350122223208517225653)
              ·
                refine ⟨322439073958425798489905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3439350122223208517225653 322439073958425798489905)
                ·
                  refine ⟨241829305468819348867429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322439073958425798489905 241829305468819348867429)
                  ·
                    rfl

theorem cell20_529831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 2].length) (baseStart_529831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529831 prefixEnd_529831 := by exact prefixLift 529831
  have htrace : WordTrace (prefixWord ++ tailWord_529831) baseStart_529831 baseEnd_529831 := by
    simpa [prefixWord, tailWord_529831, baseEnd_529831] using wordTrace_append hprefix tailTrace_529831
  have hstable : (prefixWord ++ tailWord_529831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529831).length < 2 ^ (prefixWord ++ tailWord_529831).sum := by decide
  have hdescent : baseEnd_529831 < baseStart_529831 := by decide
  rcases family_descends (prefixWord ++ tailWord_529831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529845 : List Nat := [1, 3, 3, 2, 2, 1, 1, 4, 3]
def baseStart_529845 : Nat := 118140960795 + 529845 * 2 ^ 59
def prefixEnd_529845 : Nat := 4983230072969 + 3 ^ 40 * 529845 * 2
def baseEnd_529845 : Nat := 241835695450297522400705

theorem tailTrace_529845 : CollatzResearch.WordTrace tailWord_529845 prefixEnd_529845 241835695450297522400705 := by
  unfold tailWord_529845
  simp only [CollatzResearch.WordTrace]
  refine ⟨19325034765469530166806989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12883356510313020111204659 19325034765469530166806989)
  ·
    refine ⟨7246888037051073812552621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19325034765469530166806989 7246888037051073812552621)
    ·
      refine ⟨2717583013894152679707233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7246888037051073812552621 2717583013894152679707233)
      ·
        refine ⟨2038187260420614509780425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2717583013894152679707233 2038187260420614509780425)
        ·
          refine ⟨1528640445315460882335319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2038187260420614509780425 1528640445315460882335319)
          ·
            refine ⟨2292960667973191323502979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1528640445315460882335319 2292960667973191323502979)
            ·
              refine ⟨3439441001959786985254469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2292960667973191323502979 3439441001959786985254469)
              ·
                refine ⟨644895187867460059735213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3439441001959786985254469 644895187867460059735213)
                ·
                  refine ⟨241835695450297522400705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644895187867460059735213 241835695450297522400705)
                  ·
                    rfl

theorem cell20_529845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_529845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529845 prefixEnd_529845 := by exact prefixLift 529845
  have htrace : WordTrace (prefixWord ++ tailWord_529845) baseStart_529845 baseEnd_529845 := by
    simpa [prefixWord, tailWord_529845, baseEnd_529845] using wordTrace_append hprefix tailTrace_529845
  have hstable : (prefixWord ++ tailWord_529845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529845).length < 2 ^ (prefixWord ++ tailWord_529845).sum := by decide
  have hdescent : baseEnd_529845 < baseStart_529845 := by decide
  rcases family_descends (prefixWord ++ tailWord_529845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529880 : List Nat := [2, 1, 2, 2, 2, 1, 2, 8]
def baseStart_529880 : Nat := 118140960795 + 529880 * 2 ^ 59
def prefixEnd_529880 : Nat := 4983230072969 + 3 ^ 40 * 529880 * 2
def baseEnd_529880 : Nat := 80617223467997652077965

theorem tailTrace_529880 : CollatzResearch.WordTrace tailWord_529880 prefixEnd_529880 80617223467997652077965 := by
  unfold tailWord_529880
  simp only [CollatzResearch.WordTrace]
  refine ⟨9663155660171365572165547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12884207546895154096220729 9663155660171365572165547)
  ·
    refine ⟨14494733490257048358248321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9663155660171365572165547 14494733490257048358248321)
    ·
      refine ⟨10871050117692786268686241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14494733490257048358248321 10871050117692786268686241)
      ·
        refine ⟨8153287588269589701514681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10871050117692786268686241 8153287588269589701514681)
        ·
          refine ⟨6114965691202192276136011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8153287588269589701514681 6114965691202192276136011)
          ·
            refine ⟨9172448536803288414204017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6114965691202192276136011 9172448536803288414204017)
            ·
              refine ⟨6879336402602466310653013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9172448536803288414204017 6879336402602466310653013)
              ·
                refine ⟨80617223467997652077965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6879336402602466310653013 80617223467997652077965)
                ·
                  rfl

theorem cell20_529880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_529880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529880 prefixEnd_529880 := by exact prefixLift 529880
  have htrace : WordTrace (prefixWord ++ tailWord_529880) baseStart_529880 baseEnd_529880 := by
    simpa [prefixWord, tailWord_529880, baseEnd_529880] using wordTrace_append hprefix tailTrace_529880
  have hstable : (prefixWord ++ tailWord_529880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529880).length < 2 ^ (prefixWord ++ tailWord_529880).sum := by decide
  have hdescent : baseEnd_529880 < baseStart_529880 := by decide
  rcases family_descends (prefixWord ++ tailWord_529880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529904 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 5]
def baseStart_529904 : Nat := 118140960795 + 529904 * 2 ^ 59
def prefixEnd_529904 : Nat := 4983230072969 + 3 ^ 40 * 529904 * 2
def baseEnd_529904 : Nat := 241862624657955539433797

theorem tailTrace_529904 : CollatzResearch.WordTrace tailWord_529904 prefixEnd_529904 241862624657955539433797 := by
  unfold tailWord_529904
  simp only [CollatzResearch.WordTrace]
  refine ⟨9663593336127891621602383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12884791114837188828803177 9663593336127891621602383)
  ·
    refine ⟨14495390004191837432403575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9663593336127891621602383 14495390004191837432403575)
    ·
      refine ⟨21743085006287756148605363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14495390004191837432403575 21743085006287756148605363)
      ·
        refine ⟨32614627509431634222908045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21743085006287756148605363 32614627509431634222908045)
        ·
          refine ⟨12230485316036862833590517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32614627509431634222908045 12230485316036862833590517)
          ·
            refine ⟨1146607998378455890649111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12230485316036862833590517 1146607998378455890649111)
            ·
              refine ⟨1719911997567683835973667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1146607998378455890649111 1719911997567683835973667)
              ·
                refine ⟨2579867996351525753960501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1719911997567683835973667 2579867996351525753960501)
                ·
                  refine ⟨241862624657955539433797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2579867996351525753960501 241862624657955539433797)
                  ·
                    rfl

theorem cell20_529904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_529904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529904 prefixEnd_529904 := by exact prefixLift 529904
  have htrace : WordTrace (prefixWord ++ tailWord_529904) baseStart_529904 baseEnd_529904 := by
    simpa [prefixWord, tailWord_529904, baseEnd_529904] using wordTrace_append hprefix tailTrace_529904
  have hstable : (prefixWord ++ tailWord_529904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529904).length < 2 ^ (prefixWord ++ tailWord_529904).sum := by decide
  have hdescent : baseEnd_529904 < baseStart_529904 := by decide
  rcases family_descends (prefixWord ++ tailWord_529904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529931 : List Nat := [1, 1, 1, 1, 9, 1, 2, 4]
def baseStart_529931 : Nat := 118140960795 + 529931 * 2 ^ 59
def prefixEnd_529931 : Nat := 4983230072969 + 3 ^ 40 * 529931 * 2
def baseEnd_529931 : Nat := 80624982731221148511229

theorem tailTrace_529931 : CollatzResearch.WordTrace tailWord_529931 prefixEnd_529931 80624982731221148511229 := by
  unfold tailWord_529931
  simp only [CollatzResearch.WordTrace]
  refine ⟨19328171443157966854437647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12885447628771977902958431 19328171443157966854437647)
  ·
    refine ⟨28992257164736950281656471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19328171443157966854437647 28992257164736950281656471)
    ·
      refine ⟨43488385747105425422484707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28992257164736950281656471 43488385747105425422484707)
      ·
        refine ⟨65232578620658138133727061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43488385747105425422484707 65232578620658138133727061)
        ·
          refine ⟨382222140355418778127307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 65232578620658138133727061 382222140355418778127307)
          ·
            refine ⟨573333210533128167190961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382222140355418778127307 573333210533128167190961)
            ·
              refine ⟨429999907899846125393221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573333210533128167190961 429999907899846125393221)
              ·
                refine ⟨80624982731221148511229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 429999907899846125393221 80624982731221148511229)
                ·
                  rfl

theorem cell20_529931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 4].length) (baseStart_529931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529931 prefixEnd_529931 := by exact prefixLift 529931
  have htrace : WordTrace (prefixWord ++ tailWord_529931) baseStart_529931 baseEnd_529931 := by
    simpa [prefixWord, tailWord_529931, baseEnd_529931] using wordTrace_append hprefix tailTrace_529931
  have hstable : (prefixWord ++ tailWord_529931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529931).length < 2 ^ (prefixWord ++ tailWord_529931).sum := by decide
  have hdescent : baseEnd_529931 < baseStart_529931 := by decide
  rcases family_descends (prefixWord ++ tailWord_529931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529962 : List Nat := [3, 1, 4, 1, 1, 1, 5, 2, 2]
def baseStart_529962 : Nat := 118140960795 + 529962 * 2 ^ 59
def prefixEnd_529962 : Nat := 4983230072969 + 3 ^ 40 * 529962 * 2
def baseEnd_529962 : Nat := 241889097438365115500227

theorem tailTrace_529962 : CollatzResearch.WordTrace tailWord_529962 prefixEnd_529962 241889097438365115500227 := by
  unfold tailWord_529962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4832325526511414787204035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12886201404030439432544093 4832325526511414787204035)
  ·
    refine ⟨7248488289767122180806053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4832325526511414787204035 7248488289767122180806053)
    ·
      refine ⟨1359091554331335408901135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7248488289767122180806053 1359091554331335408901135)
      ·
        refine ⟨2038637331497003113351703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1359091554331335408901135 2038637331497003113351703)
        ·
          refine ⟨3057955997245504670027555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2038637331497003113351703 3057955997245504670027555)
          ·
            refine ⟨4586933995868257005041333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3057955997245504670027555 4586933995868257005041333)
            ·
              refine ⟨430025062112649094222625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4586933995868257005041333 430025062112649094222625)
              ·
                refine ⟨322518796584486820666969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430025062112649094222625 322518796584486820666969)
                ·
                  refine ⟨241889097438365115500227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322518796584486820666969 241889097438365115500227)
                  ·
                    rfl

theorem cell20_529962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_529962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529962 prefixEnd_529962 := by exact prefixLift 529962
  have htrace : WordTrace (prefixWord ++ tailWord_529962) baseStart_529962 baseEnd_529962 := by
    simpa [prefixWord, tailWord_529962, baseEnd_529962] using wordTrace_append hprefix tailTrace_529962
  have hstable : (prefixWord ++ tailWord_529962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529962).length < 2 ^ (prefixWord ++ tailWord_529962).sum := by decide
  have hdescent : baseEnd_529962 < baseStart_529962 := by decide
  rcases family_descends (prefixWord ++ tailWord_529962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529973 : List Nat := [1, 3, 3, 1, 1, 4, 2, 5]
def baseStart_529973 : Nat := 118140960795 + 529973 * 2 ^ 59
def prefixEnd_529973 : Nat := 4983230072969 + 3 ^ 40 * 529973 * 2
def baseEnd_529973 : Nat := 80631372712699322044505

theorem tailTrace_529973 : CollatzResearch.WordTrace tailWord_529973 prefixEnd_529973 80631372712699322044505 := by
  unfold tailWord_529973
  simp only [CollatzResearch.WordTrace]
  refine ⟨19329703309005808027466573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12886468872670538684977715 19329703309005808027466573)
  ·
    refine ⟨7248638740877178010299965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19329703309005808027466573 7248638740877178010299965)
    ·
      refine ⟨2718239527828941753862487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7248638740877178010299965 2718239527828941753862487)
      ·
        refine ⟨4077359291743412630793731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2718239527828941753862487 4077359291743412630793731)
        ·
          refine ⟨6116038937615118946190597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4077359291743412630793731 6116038937615118946190597)
          ·
            refine ⟨1146757300802834802410737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6116038937615118946190597 1146757300802834802410737)
            ·
              refine ⟨860067975602126101808053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1146757300802834802410737 860067975602126101808053)
              ·
                refine ⟨80631372712699322044505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 860067975602126101808053 80631372712699322044505)
                ·
                  rfl

theorem cell20_529973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 5].length) (baseStart_529973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529973 prefixEnd_529973 := by exact prefixLift 529973
  have htrace : WordTrace (prefixWord ++ tailWord_529973) baseStart_529973 baseEnd_529973 := by
    simpa [prefixWord, tailWord_529973, baseEnd_529973] using wordTrace_append hprefix tailTrace_529973
  have hstable : (prefixWord ++ tailWord_529973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529973).length < 2 ^ (prefixWord ++ tailWord_529973).sum := by decide
  have hdescent : baseEnd_529973 < baseStart_529973 := by decide
  rcases family_descends (prefixWord ++ tailWord_529973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529976 : List Nat := [2, 1, 2, 1, 4, 4, 2, 1, 3]
def baseStart_529976 : Nat := 118140960795 + 529976 * 2 ^ 59
def prefixEnd_529976 : Nat := 4983230072969 + 3 ^ 40 * 529976 * 2
def baseEnd_529976 : Nat := 241895487419843289033503

theorem tailTrace_529976 : CollatzResearch.WordTrace tailWord_529976 prefixEnd_529976 241895487419843289033503 := by
  unfold tailWord_529976
  simp only [CollatzResearch.WordTrace]
  refine ⟨9664906363997469769912891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12886541818663293026550521 9664906363997469769912891)
  ·
    refine ⟨14497359545996204654869337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9664906363997469769912891 14497359545996204654869337)
    ·
      refine ⟨10873019659497153491152003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14497359545996204654869337 10873019659497153491152003)
      ·
        refine ⟨16309529489245730236728005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10873019659497153491152003 16309529489245730236728005)
        ·
          refine ⟨3058036779233574419386501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16309529489245730236728005 3058036779233574419386501)
          ·
            refine ⟨573381896106295203634969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3058036779233574419386501 573381896106295203634969)
            ·
              refine ⟨430036422079721402726227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573381896106295203634969 430036422079721402726227)
              ·
                refine ⟨645054633119582104089341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430036422079721402726227 645054633119582104089341)
                ·
                  refine ⟨241895487419843289033503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645054633119582104089341 241895487419843289033503)
                  ·
                    rfl

theorem cell20_529976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 3].length) (baseStart_529976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529976 prefixEnd_529976 := by exact prefixLift 529976
  have htrace : WordTrace (prefixWord ++ tailWord_529976) baseStart_529976 baseEnd_529976 := by
    simpa [prefixWord, tailWord_529976, baseEnd_529976] using wordTrace_append hprefix tailTrace_529976
  have hstable : (prefixWord ++ tailWord_529976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529976).length < 2 ^ (prefixWord ++ tailWord_529976).sum := by decide
  have hdescent : baseEnd_529976 < baseStart_529976 := by decide
  rcases family_descends (prefixWord ++ tailWord_529976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529994 : List Nat := [3, 1, 2, 1, 1, 3, 1, 8]
def baseStart_529994 : Nat := 118140960795 + 529994 * 2 ^ 59
def prefixEnd_529994 : Nat := 4983230072969 + 3 ^ 40 * 529994 * 2
def baseEnd_529994 : Nat := 80634567703438408811143

theorem tailTrace_529994 : CollatzResearch.WordTrace tailWord_529994 prefixEnd_529994 80634567703438408811143 := by
  unfold tailWord_529994
  simp only [CollatzResearch.WordTrace]
  refine ⟨4832617310482432153495259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12886979494619819075987357 4832617310482432153495259)
  ·
    refine ⟨7248925965723648230242889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4832617310482432153495259 7248925965723648230242889)
    ·
      refine ⟨5436694474292736172682167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7248925965723648230242889 5436694474292736172682167)
      ·
        refine ⟨8155041711439104259023251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5436694474292736172682167 8155041711439104259023251)
        ·
          refine ⟨12232562567158656388534877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8155041711439104259023251 12232562567158656388534877)
          ·
            refine ⟨4587210962684496145700579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12232562567158656388534877 4587210962684496145700579)
            ·
              refine ⟨6880816444026744218550869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4587210962684496145700579 6880816444026744218550869)
              ·
                refine ⟨80634567703438408811143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6880816444026744218550869 80634567703438408811143)
                ·
                  rfl

theorem cell20_529994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_529994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529994 prefixEnd_529994 := by exact prefixLift 529994
  have htrace : WordTrace (prefixWord ++ tailWord_529994) baseStart_529994 baseEnd_529994 := by
    simpa [prefixWord, tailWord_529994, baseEnd_529994] using wordTrace_append hprefix tailTrace_529994
  have hstable : (prefixWord ++ tailWord_529994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529994).length < 2 ^ (prefixWord ++ tailWord_529994).sum := by decide
  have hdescent : baseEnd_529994 < baseStart_529994 := by decide
  rcases family_descends (prefixWord ++ tailWord_529994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530013 : List Nat := [1, 4, 4, 2, 2, 1, 2, 2, 2]
def baseStart_530013 : Nat := 118140960795 + 530013 * 2 ^ 59
def prefixEnd_530013 : Nat := 4983230072969 + 3 ^ 40 * 530013 * 2
def baseEnd_530013 : Nat := 241912375228035604800019

theorem tailTrace_530013 : CollatzResearch.WordTrace tailWord_530013 prefixEnd_530013 241912375228035604800019 := by
  unfold tailWord_530013
  simp only [CollatzResearch.WordTrace]
  refine ⟨19331162228860894858922693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12887441485907263239281795 19331162228860894858922693)
  ·
    refine ⟨3624592917911417786048005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19331162228860894858922693 3624592917911417786048005)
    ·
      refine ⟨679611172108390834884001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3624592917911417786048005 679611172108390834884001)
      ·
        refine ⟨509708379081293126163001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679611172108390834884001 509708379081293126163001)
        ·
          refine ⟨382281284310969844622251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509708379081293126163001 382281284310969844622251)
          ·
            refine ⟨573421926466454766933377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382281284310969844622251 573421926466454766933377)
            ·
              refine ⟨430066444849841075200033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573421926466454766933377 430066444849841075200033)
              ·
                refine ⟨322549833637380806400025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430066444849841075200033 322549833637380806400025)
                ·
                  refine ⟨241912375228035604800019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322549833637380806400025 241912375228035604800019)
                  ·
                    rfl

theorem cell20_530013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_530013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530013 prefixEnd_530013 := by exact prefixLift 530013
  have htrace : WordTrace (prefixWord ++ tailWord_530013) baseStart_530013 baseEnd_530013 := by
    simpa [prefixWord, tailWord_530013, baseEnd_530013] using wordTrace_append hprefix tailTrace_530013
  have hstable : (prefixWord ++ tailWord_530013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530013).length < 2 ^ (prefixWord ++ tailWord_530013).sum := by decide
  have hdescent : baseEnd_530013 < baseStart_530013 := by decide
  rcases family_descends (prefixWord ++ tailWord_530013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530021 : List Nat := [1, 3, 1, 3, 3, 2, 1, 4, 2]
def baseStart_530021 : Nat := 118140960795 + 530021 * 2 ^ 59
def prefixEnd_530021 : Nat := 4983230072969 + 3 ^ 40 * 530021 * 2
def baseEnd_530021 : Nat := 241916026646023132533319

theorem tailTrace_530021 : CollatzResearch.WordTrace tailWord_530021 prefixEnd_530021 241916026646023132533319 := by
  unfold tailWord_530021
  simp only [CollatzResearch.WordTrace]
  refine ⟨19331454012831912225213917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12887636008554608150142611 19331454012831912225213917)
  ·
    refine ⟨7249295254811967084455219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19331454012831912225213917 7249295254811967084455219)
    ·
      refine ⟨10873942882217950626682829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7249295254811967084455219 10873942882217950626682829)
      ·
        refine ⟨4077728580831731485006061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10873942882217950626682829 4077728580831731485006061)
        ·
          refine ⟨1529148217811899306877273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4077728580831731485006061 1529148217811899306877273)
          ·
            refine ⟨1146861163358924480157955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1529148217811899306877273 1146861163358924480157955)
            ·
              refine ⟨1720291745038386720236933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1146861163358924480157955 1720291745038386720236933)
              ·
                refine ⟨322554702194697510044425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1720291745038386720236933 322554702194697510044425)
                ·
                  refine ⟨241916026646023132533319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322554702194697510044425 241916026646023132533319)
                  ·
                    rfl

theorem cell20_530021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_530021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530021 prefixEnd_530021 := by exact prefixLift 530021
  have htrace : WordTrace (prefixWord ++ tailWord_530021) baseStart_530021 baseEnd_530021 := by
    simpa [prefixWord, tailWord_530021, baseEnd_530021] using wordTrace_append hprefix tailTrace_530021
  have hstable : (prefixWord ++ tailWord_530021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530021).length < 2 ^ (prefixWord ++ tailWord_530021).sum := by decide
  have hdescent : baseEnd_530021 < baseStart_530021 := by decide
  rcases family_descends (prefixWord ++ tailWord_530021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530039 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 7]
def baseStart_530039 : Nat := 118140960795 + 530039 * 2 ^ 59
def prefixEnd_530039 : Nat := 4983230072969 + 3 ^ 40 * 530039 * 2
def baseEnd_530039 : Nat := 241924242336495069933245

theorem tailTrace_530039 : CollatzResearch.WordTrace tailWord_530039 prefixEnd_530039 241924242336495069933245 := by
  unfold tailWord_530039
  simp only [CollatzResearch.WordTrace]
  refine ⟨19332110526766701299369171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12888073684511134199579447 19332110526766701299369171)
  ·
    refine ⟨28998165790150051949053757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19332110526766701299369171 28998165790150051949053757)
    ·
      refine ⟨10874312171306269480895159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28998165790150051949053757 10874312171306269480895159)
      ·
        refine ⟨16311468256959404221342739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10874312171306269480895159 16311468256959404221342739)
        ·
          refine ⟨24467202385439106332014109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16311468256959404221342739 24467202385439106332014109)
          ·
            refine ⟨9175200894539664874505291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24467202385439106332014109 9175200894539664874505291)
            ·
              refine ⟨13762801341809497311757937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9175200894539664874505291 13762801341809497311757937)
              ·
                refine ⟨10322101006357122983818453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13762801341809497311757937 10322101006357122983818453)
                ·
                  refine ⟨241924242336495069933245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10322101006357122983818453 241924242336495069933245)
                  ·
                    rfl

theorem cell20_530039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_530039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530039 prefixEnd_530039 := by exact prefixLift 530039
  have htrace : WordTrace (prefixWord ++ tailWord_530039) baseStart_530039 baseEnd_530039 := by
    simpa [prefixWord, tailWord_530039, baseEnd_530039] using wordTrace_append hprefix tailTrace_530039
  have hstable : (prefixWord ++ tailWord_530039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530039).length < 2 ^ (prefixWord ++ tailWord_530039).sum := by decide
  have hdescent : baseEnd_530039 < baseStart_530039 := by decide
  rcases family_descends (prefixWord ++ tailWord_530039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530080 : List Nat := [2, 1, 1, 4, 3, 2, 2, 1, 4]
def baseStart_530080 : Nat := 118140960795 + 530080 * 2 ^ 59
def prefixEnd_530080 : Nat := 4983230072969 + 3 ^ 40 * 530080 * 2
def baseEnd_530080 : Nat := 241942955853681149566411

theorem tailTrace_530080 : CollatzResearch.WordTrace tailWord_530080 prefixEnd_530080 241942955853681149566411 := by
  unfold tailWord_530080
  simp only [CollatzResearch.WordTrace]
  refine ⟨9666802959809082650805847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12889070613078776867741129 9666802959809082650805847)
  ·
    refine ⟨14500204439713623976208771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9666802959809082650805847 14500204439713623976208771)
    ·
      refine ⟨21750306659570435964313157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14500204439713623976208771 21750306659570435964313157)
      ·
        refine ⟨4078182498669456743308717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21750306659570435964313157 4078182498669456743308717)
        ·
          refine ⟨1529318437001046278740769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4078182498669456743308717 1529318437001046278740769)
          ·
            refine ⟨1146988827750784709055577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1529318437001046278740769 1146988827750784709055577)
            ·
              refine ⟨860241620813088531791683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1146988827750784709055577 860241620813088531791683)
              ·
                refine ⟨1290362431219632797687525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 860241620813088531791683 1290362431219632797687525)
                ·
                  refine ⟨241942955853681149566411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1290362431219632797687525 241942955853681149566411)
                  ·
                    rfl

theorem cell20_530080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_530080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530080 prefixEnd_530080 := by exact prefixLift 530080
  have htrace : WordTrace (prefixWord ++ tailWord_530080) baseStart_530080 baseEnd_530080 := by
    simpa [prefixWord, tailWord_530080, baseEnd_530080] using wordTrace_append hprefix tailTrace_530080
  have hstable : (prefixWord ++ tailWord_530080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530080).length < 2 ^ (prefixWord ++ tailWord_530080).sum := by decide
  have hdescent : baseEnd_530080 < baseStart_530080 := by decide
  rcases family_descends (prefixWord ++ tailWord_530080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530135 : List Nat := [1, 1, 3, 2, 1, 3, 5, 2, 2]
def baseStart_530135 : Nat := 118140960795 + 530135 * 2 ^ 59
def prefixEnd_530135 : Nat := 4983230072969 + 3 ^ 40 * 530135 * 2
def baseEnd_530135 : Nat := 241968059352345402732853

theorem tailTrace_530135 : CollatzResearch.WordTrace tailWord_530135 prefixEnd_530135 241968059352345402732853 := by
  unfold tailWord_530135
  simp only [CollatzResearch.WordTrace]
  refine ⟨19335611934418909694863859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12890407956279273129909239 19335611934418909694863859)
  ·
    refine ⟨29003417901628364542295789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19335611934418909694863859 29003417901628364542295789)
    ·
      refine ⟨10876281713110636703360921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29003417901628364542295789 10876281713110636703360921)
      ·
        refine ⟨8157211284832977527520691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10876281713110636703360921 8157211284832977527520691)
        ·
          refine ⟨12235816927249466291281037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8157211284832977527520691 12235816927249466291281037)
          ·
            refine ⟨4588431347718549859230389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12235816927249466291281037 4588431347718549859230389)
            ·
              refine ⟨430165438848614049302849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4588431347718549859230389 430165438848614049302849)
              ·
                refine ⟨322624079136460536977137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430165438848614049302849 322624079136460536977137)
                ·
                  refine ⟨241968059352345402732853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322624079136460536977137 241968059352345402732853)
                  ·
                    rfl

theorem cell20_530135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 2].length) (baseStart_530135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530135 prefixEnd_530135 := by exact prefixLift 530135
  have htrace : WordTrace (prefixWord ++ tailWord_530135) baseStart_530135 baseEnd_530135 := by
    simpa [prefixWord, tailWord_530135, baseEnd_530135] using wordTrace_append hprefix tailTrace_530135
  have hstable : (prefixWord ++ tailWord_530135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530135).length < 2 ^ (prefixWord ++ tailWord_530135).sum := by decide
  have hdescent : baseEnd_530135 < baseStart_530135 := by decide
  rcases family_descends (prefixWord ++ tailWord_530135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530145 : List Nat := [1, 2, 3, 1, 6, 1, 2, 1, 3]
def baseStart_530145 : Nat := 118140960795 + 530145 * 2 ^ 59
def prefixEnd_530145 : Nat := 4983230072969 + 3 ^ 40 * 530145 * 2
def baseEnd_530145 : Nat := 241972623624829812399479

theorem tailTrace_530145 : CollatzResearch.WordTrace tailWord_530145 prefixEnd_530145 241972623624829812399479 := by
  unfold tailWord_530145
  simp only [CollatzResearch.WordTrace]
  refine ⟨19335976664382681402727889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12890651109588454268485259 19335976664382681402727889)
  ·
    refine ⟨14501982498287011052045917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19335976664382681402727889 14501982498287011052045917)
    ·
      refine ⟨5438243436857629144517219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14501982498287011052045917 5438243436857629144517219)
      ·
        refine ⟨8157365155286443716775829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5438243436857629144517219 8157365155286443716775829)
        ·
          refine ⟨382376491654052049223867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8157365155286443716775829 382376491654052049223867)
          ·
            refine ⟨573564737481078073835801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382376491654052049223867 573564737481078073835801)
            ·
              refine ⟨430173553110808555376851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573564737481078073835801 430173553110808555376851)
              ·
                refine ⟨645260329666212833065277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430173553110808555376851 645260329666212833065277)
                ·
                  refine ⟨241972623624829812399479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645260329666212833065277 241972623624829812399479)
                  ·
                    rfl

theorem cell20_530145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 3].length) (baseStart_530145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530145 prefixEnd_530145 := by exact prefixLift 530145
  have htrace : WordTrace (prefixWord ++ tailWord_530145) baseStart_530145 baseEnd_530145 := by
    simpa [prefixWord, tailWord_530145, baseEnd_530145] using wordTrace_append hprefix tailTrace_530145
  have hstable : (prefixWord ++ tailWord_530145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530145).length < 2 ^ (prefixWord ++ tailWord_530145).sum := by decide
  have hdescent : baseEnd_530145 < baseStart_530145 := by decide
  rcases family_descends (prefixWord ++ tailWord_530145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530208 : List Nat := [2, 1, 1, 5, 1, 1, 1, 5, 3]
def baseStart_530208 : Nat := 118140960795 + 530208 * 2 ^ 59
def prefixEnd_530208 : Nat := 4983230072969 + 3 ^ 40 * 530208 * 2
def baseEnd_530208 : Nat := 242001378541481593299221

theorem tailTrace_530208 : CollatzResearch.WordTrace tailWord_530208 prefixEnd_530208 242001378541481593299221 := by
  unfold tailWord_530208
  simp only [CollatzResearch.WordTrace]
  refine ⟨9669137231577221581135639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12892182975436295441514185 9669137231577221581135639)
  ·
    refine ⟨14503705847365832371703459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9669137231577221581135639 14503705847365832371703459)
    ·
      refine ⟨21755558771048748557555189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14503705847365832371703459 21755558771048748557555189)
      ·
        refine ⟨2039583634785820177270799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21755558771048748557555189 2039583634785820177270799)
        ·
          refine ⟨3059375452178730265906199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2039583634785820177270799 3059375452178730265906199)
          ·
            refine ⟨4589063178268095398859299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3059375452178730265906199 4589063178268095398859299)
            ·
              refine ⟨6883594767402143098288949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4589063178268095398859299 6883594767402143098288949)
              ·
                refine ⟨645337009443950915464589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6883594767402143098288949 645337009443950915464589)
                ·
                  refine ⟨242001378541481593299221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645337009443950915464589 242001378541481593299221)
                  ·
                    rfl

theorem cell20_530208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_530208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530208 prefixEnd_530208 := by exact prefixLift 530208
  have htrace : WordTrace (prefixWord ++ tailWord_530208) baseStart_530208 baseEnd_530208 := by
    simpa [prefixWord, tailWord_530208, baseEnd_530208] using wordTrace_append hprefix tailTrace_530208
  have hstable : (prefixWord ++ tailWord_530208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530208).length < 2 ^ (prefixWord ++ tailWord_530208).sum := by decide
  have hdescent : baseEnd_530208 < baseStart_530208 := by decide
  rcases family_descends (prefixWord ++ tailWord_530208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530228 : List Nat := [2, 5, 1, 1, 2, 2, 2, 3, 2]
def baseStart_530228 : Nat := 118140960795 + 530228 * 2 ^ 59
def prefixEnd_530228 : Nat := 4983230072969 + 3 ^ 40 * 530228 * 2
def baseEnd_530228 : Nat := 242010507086450412632473

theorem tailTrace_530228 : CollatzResearch.WordTrace tailWord_530228 prefixEnd_530228 242010507086450412632473 := by
  unfold tailWord_530228
  simp only [CollatzResearch.WordTrace]
  refine ⟨9669501961540993288999669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12892669282054657718666225 9669501961540993288999669)
  ·
    refine ⟨906515808894468120843719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9669501961540993288999669 906515808894468120843719)
    ·
      refine ⟨1359773713341702181265579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 906515808894468120843719 1359773713341702181265579)
      ·
        refine ⟨2039660570012553271898369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1359773713341702181265579 2039660570012553271898369)
        ·
          refine ⟨1529745427509414953923777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2039660570012553271898369 1529745427509414953923777)
          ·
            refine ⟨1147309070632061215442833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1529745427509414953923777 1147309070632061215442833)
            ·
              refine ⟨860481802974045911582125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1147309070632061215442833 860481802974045911582125)
              ·
                refine ⟨322680676115267216843297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 860481802974045911582125 322680676115267216843297)
                ·
                  refine ⟨242010507086450412632473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322680676115267216843297 242010507086450412632473)
                  ·
                    rfl

theorem cell20_530228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_530228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530228 prefixEnd_530228 := by exact prefixLift 530228
  have htrace : WordTrace (prefixWord ++ tailWord_530228) baseStart_530228 baseEnd_530228 := by
    simpa [prefixWord, tailWord_530228, baseEnd_530228] using wordTrace_append hprefix tailTrace_530228
  have hstable : (prefixWord ++ tailWord_530228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530228).length < 2 ^ (prefixWord ++ tailWord_530228).sum := by decide
  have hdescent : baseEnd_530228 < baseStart_530228 := by decide
  rcases family_descends (prefixWord ++ tailWord_530228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530232 : List Nat := [2, 1, 2, 1, 3, 3, 1, 5, 2]
def baseStart_530232 : Nat := 118140960795 + 530232 * 2 ^ 59
def prefixEnd_530232 : Nat := 4983230072969 + 3 ^ 40 * 530232 * 2
def baseEnd_530232 : Nat := 242012332795444176499123

theorem tailTrace_530232 : CollatzResearch.WordTrace tailWord_530232 prefixEnd_530232 242012332795444176499123 := by
  unfold tailWord_530232
  simp only [CollatzResearch.WordTrace]
  refine ⟨9669574907533747630572475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12892766543378330174096633 9669574907533747630572475)
  ·
    refine ⟨14504362361300621445858713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9669574907533747630572475 14504362361300621445858713)
    ·
      refine ⟨10878271770975466084394035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14504362361300621445858713 10878271770975466084394035)
      ·
        refine ⟨16317407656463199126591053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10878271770975466084394035 16317407656463199126591053)
        ·
          refine ⟨6119027871173699672471645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16317407656463199126591053 6119027871173699672471645)
          ·
            refine ⟨2294635451690137377176867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6119027871173699672471645 2294635451690137377176867)
            ·
              refine ⟨3441953177535206065765301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2294635451690137377176867 3441953177535206065765301)
              ·
                refine ⟨322683110393925568665497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3441953177535206065765301 322683110393925568665497)
                ·
                  refine ⟨242012332795444176499123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322683110393925568665497 242012332795444176499123)
                  ·
                    rfl

theorem cell20_530232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 2].length) (baseStart_530232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530232 prefixEnd_530232 := by exact prefixLift 530232
  have htrace : WordTrace (prefixWord ++ tailWord_530232) baseStart_530232 baseEnd_530232 := by
    simpa [prefixWord, tailWord_530232, baseEnd_530232] using wordTrace_append hprefix tailTrace_530232
  have hstable : (prefixWord ++ tailWord_530232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530232).length < 2 ^ (prefixWord ++ tailWord_530232).sum := by decide
  have hdescent : baseEnd_530232 < baseStart_530232 := by decide
  rcases family_descends (prefixWord ++ tailWord_530232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530294 : List Nat := [5, 1, 1, 3, 2, 2, 6]
def baseStart_530294 : Nat := 118140960795 + 530294 * 2 ^ 59
def prefixEnd_530294 : Nat := 4983230072969 + 3 ^ 40 * 530294 * 2
def baseEnd_530294 : Nat := 26893403476094168492467

theorem tailTrace_530294 : CollatzResearch.WordTrace tailWord_530294 prefixEnd_530294 26893403476094168492467 := by
  unfold tailWord_530294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1208838196302679990618871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12894274093895253233267957 1208838196302679990618871)
  ·
    refine ⟨1813257294454019985928307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1208838196302679990618871 1813257294454019985928307)
    ·
      refine ⟨2719885941681029978892461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1813257294454019985928307 2719885941681029978892461)
      ·
        refine ⟨1019957228130386242084673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2719885941681029978892461 1019957228130386242084673)
        ·
          refine ⟨764967921097789681563505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1019957228130386242084673 764967921097789681563505)
          ·
            refine ⟨573725940823342261172629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764967921097789681563505 573725940823342261172629)
            ·
              refine ⟨26893403476094168492467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 573725940823342261172629 26893403476094168492467)
              ·
                rfl

theorem cell20_530294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 6].length) (baseStart_530294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530294 prefixEnd_530294 := by exact prefixLift 530294
  have htrace : WordTrace (prefixWord ++ tailWord_530294) baseStart_530294 baseEnd_530294 := by
    simpa [prefixWord, tailWord_530294, baseEnd_530294] using wordTrace_append hprefix tailTrace_530294
  have hstable : (prefixWord ++ tailWord_530294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530294).length < 2 ^ (prefixWord ++ tailWord_530294).sum := by decide
  have hdescent : baseEnd_530294 < baseStart_530294 := by decide
  rcases family_descends (prefixWord ++ tailWord_530294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530308 : List Nat := [2, 3, 2, 1, 1, 1, 2, 6, 2]
def baseStart_530308 : Nat := 118140960795 + 530308 * 2 ^ 59
def prefixEnd_530308 : Nat := 4983230072969 + 3 ^ 40 * 530308 * 2
def baseEnd_530308 : Nat := 242047021266325689965479

theorem tailTrace_530308 : CollatzResearch.WordTrace tailWord_530308 prefixEnd_530308 242047021266325689965479 := by
  unfold tailWord_530308
  simp only [CollatzResearch.WordTrace]
  refine ⟨9670960881396080120455789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12894614508528106827274385 9670960881396080120455789)
  ·
    refine ⟨3626610330523530045170921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9670960881396080120455789 3626610330523530045170921)
    ·
      refine ⟨2719957747892647533878191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3626610330523530045170921 2719957747892647533878191)
      ·
        refine ⟨4079936621838971300817287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2719957747892647533878191 4079936621838971300817287)
        ·
          refine ⟨6119904932758456951225931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4079936621838971300817287 6119904932758456951225931)
          ·
            refine ⟨9179857399137685426838897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6119904932758456951225931 9179857399137685426838897)
            ·
              refine ⟨6884893049353264070129173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9179857399137685426838897 6884893049353264070129173)
              ·
                refine ⟨322729361688434253287305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6884893049353264070129173 322729361688434253287305)
                ·
                  refine ⟨242047021266325689965479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322729361688434253287305 242047021266325689965479)
                  ·
                    rfl

theorem cell20_530308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_530308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530308 prefixEnd_530308 := by exact prefixLift 530308
  have htrace : WordTrace (prefixWord ++ tailWord_530308) baseStart_530308 baseEnd_530308 := by
    simpa [prefixWord, tailWord_530308, baseEnd_530308] using wordTrace_append hprefix tailTrace_530308
  have hstable : (prefixWord ++ tailWord_530308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530308).length < 2 ^ (prefixWord ++ tailWord_530308).sum := by decide
  have hdescent : baseEnd_530308 < baseStart_530308 := by decide
  rcases family_descends (prefixWord ++ tailWord_530308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530318 : List Nat := [4, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_530318 : Nat := 118140960795 + 530318 * 2 ^ 59
def prefixEnd_530318 : Nat := 4983230072969 + 3 ^ 40 * 530318 * 2
def baseEnd_530318 : Nat := 242051585538810099632105

theorem tailTrace_530318 : CollatzResearch.WordTrace tailWord_530318 prefixEnd_530318 242051585538810099632105 := by
  unfold tailWord_530318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2417785811594491493596951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12894857661837287965850405 2417785811594491493596951)
  ·
    refine ⟨3626678717391737240395427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2417785811594491493596951 3626678717391737240395427)
    ·
      refine ⟨5440018076087605860593141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3626678717391737240395427 5440018076087605860593141)
      ·
        refine ⟨510001694633213049430607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5440018076087605860593141 510001694633213049430607)
        ·
          refine ⟨765002541949819574145911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510001694633213049430607 765002541949819574145911)
          ·
            refine ⟨1147503812924729361218867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765002541949819574145911 1147503812924729361218867)
            ·
              refine ⟨1721255719387094041828301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147503812924729361218867 1721255719387094041828301)
              ·
                refine ⟨645470894770160265685613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1721255719387094041828301 645470894770160265685613)
                ·
                  refine ⟨242051585538810099632105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645470894770160265685613 242051585538810099632105)
                  ·
                    rfl

theorem cell20_530318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_530318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530318 prefixEnd_530318 := by exact prefixLift 530318
  have htrace : WordTrace (prefixWord ++ tailWord_530318) baseStart_530318 baseEnd_530318 := by
    simpa [prefixWord, tailWord_530318, baseEnd_530318] using wordTrace_append hprefix tailTrace_530318
  have hstable : (prefixWord ++ tailWord_530318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530318).length < 2 ^ (prefixWord ++ tailWord_530318).sum := by decide
  have hdescent : baseEnd_530318 < baseStart_530318 := by decide
  rcases family_descends (prefixWord ++ tailWord_530318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530360 : List Nat := [2, 1, 2, 1, 2, 3, 4, 2, 3]
def baseStart_530360 : Nat := 118140960795 + 530360 * 2 ^ 59
def prefixEnd_530360 : Nat := 4983230072969 + 3 ^ 40 * 530360 * 2
def baseEnd_530360 : Nat := 242070755483244620231933

theorem tailTrace_530360 : CollatzResearch.WordTrace tailWord_530360 prefixEnd_530360 242070755483244620231933 := by
  unfold tailWord_530360
  simp only [CollatzResearch.WordTrace]
  refine ⟨9671909179301886560902267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12895878905735848747869689 9671909179301886560902267)
  ·
    refine ⟨14507863768952829841353401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9671909179301886560902267 14507863768952829841353401)
    ·
      refine ⟨10880897826714622381015051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14507863768952829841353401 10880897826714622381015051)
      ·
        refine ⟨16321346740071933571522577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10880897826714622381015051 16321346740071933571522577)
        ·
          refine ⟨12241010055053950178641933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16321346740071933571522577 12241010055053950178641933)
          ·
            refine ⟨4590378770645231316990725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12241010055053950178641933 4590378770645231316990725)
            ·
              refine ⟨860696019495980871935761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4590378770645231316990725 860696019495980871935761)
              ·
                refine ⟨645522014621985653951821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 860696019495980871935761 645522014621985653951821)
                ·
                  refine ⟨242070755483244620231933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645522014621985653951821 242070755483244620231933)
                  ·
                    rfl

theorem cell20_530360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_530360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530360 prefixEnd_530360 := by exact prefixLift 530360
  have htrace : WordTrace (prefixWord ++ tailWord_530360) baseStart_530360 baseEnd_530360 := by
    simpa [prefixWord, tailWord_530360, baseEnd_530360] using wordTrace_append hprefix tailTrace_530360
  have hstable : (prefixWord ++ tailWord_530360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530360).length < 2 ^ (prefixWord ++ tailWord_530360).sum := by decide
  have hdescent : baseEnd_530360 < baseStart_530360 := by decide
  rcases family_descends (prefixWord ++ tailWord_530360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530438 : List Nat := [6, 2, 1, 2, 2, 1, 2, 4]
def baseStart_530438 : Nat := 118140960795 + 530438 * 2 ^ 59
def prefixEnd_530438 : Nat := 4983230072969 + 3 ^ 40 * 530438 * 2
def baseEnd_530438 : Nat := 80702118936207671877205

theorem tailTrace_530438 : CollatzResearch.WordTrace tailWord_530438 prefixEnd_530438 80702118936207671877205 := by
  unfold tailWord_530438
  simp only [CollatzResearch.WordTrace]
  refine ⟨604583226635037263848249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12897775501547461628762645 604583226635037263848249)
  ·
    refine ⟨453437419976277947886187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 604583226635037263848249 453437419976277947886187)
    ·
      refine ⟨680156129964416921829281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453437419976277947886187 680156129964416921829281)
      ·
        refine ⟨510117097473312691371961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680156129964416921829281 510117097473312691371961)
        ·
          refine ⟨382587823104984518528971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510117097473312691371961 382587823104984518528971)
          ·
            refine ⟨573881734657476777793457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382587823104984518528971 573881734657476777793457)
            ·
              refine ⟨430411300993107583345093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573881734657476777793457 430411300993107583345093)
              ·
                refine ⟨80702118936207671877205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 430411300993107583345093 80702118936207671877205)
                ·
                  rfl

theorem cell20_530438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_530438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530438 prefixEnd_530438 := by exact prefixLift 530438
  have htrace : WordTrace (prefixWord ++ tailWord_530438) baseStart_530438 baseEnd_530438 := by
    simpa [prefixWord, tailWord_530438, baseEnd_530438] using wordTrace_append hprefix tailTrace_530438
  have hstable : (prefixWord ++ tailWord_530438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530438).length < 2 ^ (prefixWord ++ tailWord_530438).sum := by decide
  have hdescent : baseEnd_530438 < baseStart_530438 := by decide
  rcases family_descends (prefixWord ++ tailWord_530438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530452 : List Nat := [2, 4, 3, 2, 2, 1, 1, 3, 2]
def baseStart_530452 : Nat := 118140960795 + 530452 * 2 ^ 59
def prefixEnd_530452 : Nat := 4983230072969 + 3 ^ 40 * 530452 * 2
def baseEnd_530452 : Nat := 242112746790101189164891

theorem tailTrace_530452 : CollatzResearch.WordTrace tailWord_530452 prefixEnd_530452 242112746790101189164891 := by
  unfold tailWord_530452
  simp only [CollatzResearch.WordTrace]
  refine ⟨9673586937135236417076805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12898115916180315222769073 9673586937135236417076805)
  ·
    refine ⟨1813797550712856828201901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9673586937135236417076805 1813797550712856828201901)
    ·
      refine ⟨680174081517321310575713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1813797550712856828201901 680174081517321310575713)
      ·
        refine ⟨510130561137990982931785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680174081517321310575713 510130561137990982931785)
        ·
          refine ⟨382597920853493237198839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510130561137990982931785 382597920853493237198839)
          ·
            refine ⟨573896881280239855798259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382597920853493237198839 573896881280239855798259)
            ·
              refine ⟨860845321920359783697389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573896881280239855798259 860845321920359783697389)
              ·
                refine ⟨322816995720134918886521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 860845321920359783697389 322816995720134918886521)
                ·
                  refine ⟨242112746790101189164891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322816995720134918886521 242112746790101189164891)
                  ·
                    rfl

theorem cell20_530452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_530452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530452 prefixEnd_530452 := by exact prefixLift 530452
  have htrace : WordTrace (prefixWord ++ tailWord_530452) baseStart_530452 baseEnd_530452 := by
    simpa [prefixWord, tailWord_530452, baseEnd_530452] using wordTrace_append hprefix tailTrace_530452
  have hstable : (prefixWord ++ tailWord_530452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530452).length < 2 ^ (prefixWord ++ tailWord_530452).sum := by decide
  have hdescent : baseEnd_530452 < baseStart_530452 := by decide
  rcases family_descends (prefixWord ++ tailWord_530452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530474 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_530474 : Nat := 118140960795 + 530474 * 2 ^ 59
def prefixEnd_530474 : Nat := 4983230072969 + 3 ^ 40 * 530474 * 2
def baseEnd_530474 : Nat := 242122788189566890431467

theorem tailTrace_530474 : CollatzResearch.WordTrace tailWord_530474 prefixEnd_530474 242122788189566890431467 := by
  unfold tailWord_530474
  simp only [CollatzResearch.WordTrace]
  refine ⟨4836994070047692647863619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12898650853460513727636317 4836994070047692647863619)
  ·
    refine ⟨7255491105071538971795429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4836994070047692647863619 7255491105071538971795429)
    ·
      refine ⟨1360404582200913557211643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7255491105071538971795429 1360404582200913557211643)
      ·
        refine ⟨2040606873301370335817465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1360404582200913557211643 2040606873301370335817465)
        ·
          refine ⟨1530455154976027751863099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2040606873301370335817465 1530455154976027751863099)
          ·
            refine ⟨2295682732464041627794649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530455154976027751863099 2295682732464041627794649)
            ·
              refine ⟨1721762049348031220845987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2295682732464041627794649 1721762049348031220845987)
              ·
                refine ⟨2582643074022046831268981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1721762049348031220845987 2582643074022046831268981)
                ·
                  refine ⟨242122788189566890431467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2582643074022046831268981 242122788189566890431467)
                  ·
                    rfl

theorem cell20_530474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_530474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530474 prefixEnd_530474 := by exact prefixLift 530474
  have htrace : WordTrace (prefixWord ++ tailWord_530474) baseStart_530474 baseEnd_530474 := by
    simpa [prefixWord, tailWord_530474, baseEnd_530474] using wordTrace_append hprefix tailTrace_530474
  have hstable : (prefixWord ++ tailWord_530474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530474).length < 2 ^ (prefixWord ++ tailWord_530474).sum := by decide
  have hdescent : baseEnd_530474 < baseStart_530474 := by decide
  rcases family_descends (prefixWord ++ tailWord_530474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530481 : List Nat := [1, 2, 2, 3, 1, 3, 3, 1, 4]
def baseStart_530481 : Nat := 118140960795 + 530481 * 2 ^ 59
def prefixEnd_530481 : Nat := 4983230072969 + 3 ^ 40 * 530481 * 2
def baseEnd_530481 : Nat := 242125983180305977198105

theorem tailTrace_530481 : CollatzResearch.WordTrace tailWord_530481 prefixEnd_530481 242125983180305977198105 := by
  unfold tailWord_530481
  simp only [CollatzResearch.WordTrace]
  refine ⟨19348231591165410786959297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12898821060776940524639531 19348231591165410786959297)
  ·
    refine ⟨14511173693374058090219473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19348231591165410786959297 14511173693374058090219473)
    ·
      refine ⟨10883380270030543567664605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14511173693374058090219473 10883380270030543567664605)
      ·
        refine ⟨4081267601261453837874227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10883380270030543567664605 4081267601261453837874227)
        ·
          refine ⟨6121901401892180756811341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4081267601261453837874227 6121901401892180756811341)
          ·
            refine ⟨2295713025709567783804253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6121901401892180756811341 2295713025709567783804253)
            ·
              refine ⟨860892384641087918926595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2295713025709567783804253 860892384641087918926595)
              ·
                refine ⟨1291338576961631878389893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 860892384641087918926595 1291338576961631878389893)
                ·
                  refine ⟨242125983180305977198105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1291338576961631878389893 242125983180305977198105)
                  ·
                    rfl

theorem cell20_530481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_530481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530481 prefixEnd_530481 := by exact prefixLift 530481
  have htrace : WordTrace (prefixWord ++ tailWord_530481) baseStart_530481 baseEnd_530481 := by
    simpa [prefixWord, tailWord_530481, baseEnd_530481] using wordTrace_append hprefix tailTrace_530481
  have hstable : (prefixWord ++ tailWord_530481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530481).length < 2 ^ (prefixWord ++ tailWord_530481).sum := by decide
  have hdescent : baseEnd_530481 < baseStart_530481 := by decide
  rcases family_descends (prefixWord ++ tailWord_530481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530484 : List Nat := [2, 5, 1, 2, 2, 1, 2, 5]
def baseStart_530484 : Nat := 118140960795 + 530484 * 2 ^ 59
def prefixEnd_530484 : Nat := 4983230072969 + 3 ^ 40 * 530484 * 2
def baseEnd_530484 : Nat := 80709117487350433366031

theorem tailTrace_530484 : CollatzResearch.WordTrace tailWord_530484 prefixEnd_530484 80709117487350433366031 := by
  unfold tailWord_530484
  simp only [CollatzResearch.WordTrace]
  refine ⟨9674170505077271149659253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12898894006769694866212337 9674170505077271149659253)
  ·
    refine ⟨906953484850994170280555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9674170505077271149659253 906953484850994170280555)
    ·
      refine ⟨1360430227276491255420833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 906953484850994170280555 1360430227276491255420833)
      ·
        refine ⟨1020322670457368441565625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1360430227276491255420833 1020322670457368441565625)
        ·
          refine ⟨765242002843026331174219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1020322670457368441565625 765242002843026331174219)
          ·
            refine ⟨1147863004264539496761329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765242002843026331174219 1147863004264539496761329)
            ·
              refine ⟨860897253198404622570997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1147863004264539496761329 860897253198404622570997)
              ·
                refine ⟨80709117487350433366031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 860897253198404622570997 80709117487350433366031)
                ·
                  rfl

theorem cell20_530484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_530484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530484 prefixEnd_530484 := by exact prefixLift 530484
  have htrace : WordTrace (prefixWord ++ tailWord_530484) baseStart_530484 baseEnd_530484 := by
    simpa [prefixWord, tailWord_530484, baseEnd_530484] using wordTrace_append hprefix tailTrace_530484
  have hstable : (prefixWord ++ tailWord_530484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530484).length < 2 ^ (prefixWord ++ tailWord_530484).sum := by decide
  have hdescent : baseEnd_530484 < baseStart_530484 := by decide
  rcases family_descends (prefixWord ++ tailWord_530484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530557 : List Nat := [1, 4, 1, 1, 3, 3, 1, 2, 4]
def baseStart_530557 : Nat := 118140960795 + 530557 * 2 ^ 59
def prefixEnd_530557 : Nat := 4983230072969 + 3 ^ 40 * 530557 * 2
def baseEnd_530557 : Nat := 242160671651187490664461

theorem tailTrace_530557 : CollatzResearch.WordTrace tailWord_530557 prefixEnd_530557 242160671651187490664461 := by
  unfold tailWord_530557
  simp only [CollatzResearch.WordTrace]
  refine ⟨19351003538890075766725925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12900669025926717177817283 19351003538890075766725925)
  ·
    refine ⟨3628313163541889206261111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19351003538890075766725925 3628313163541889206261111)
    ·
      refine ⟨5442469745312833809391667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3628313163541889206261111 5442469745312833809391667)
      ·
        refine ⟨8163704617969250714087501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5442469745312833809391667 8163704617969250714087501)
        ·
          refine ⟨3061389231738469017782813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8163704617969250714087501 3061389231738469017782813)
          ·
            refine ⟨1148020961901925881668555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3061389231738469017782813 1148020961901925881668555)
            ·
              refine ⟨1722031442852888822502833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148020961901925881668555 1722031442852888822502833)
              ·
                refine ⟨1291523582139666616877125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1722031442852888822502833 1291523582139666616877125)
                ·
                  refine ⟨242160671651187490664461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1291523582139666616877125 242160671651187490664461)
                  ·
                    rfl

theorem cell20_530557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_530557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530557 prefixEnd_530557 := by exact prefixLift 530557
  have htrace : WordTrace (prefixWord ++ tailWord_530557) baseStart_530557 baseEnd_530557 := by
    simpa [prefixWord, tailWord_530557, baseEnd_530557] using wordTrace_append hprefix tailTrace_530557
  have hstable : (prefixWord ++ tailWord_530557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530557).length < 2 ^ (prefixWord ++ tailWord_530557).sum := by decide
  have hdescent : baseEnd_530557 < baseStart_530557 := by decide
  rcases family_descends (prefixWord ++ tailWord_530557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530584 : List Nat := [2, 1, 2, 4, 4, 1, 1, 2, 3]
def baseStart_530584 : Nat := 118140960795 + 530584 * 2 ^ 59
def prefixEnd_530584 : Nat := 4983230072969 + 3 ^ 40 * 530584 * 2
def baseEnd_530584 : Nat := 242172995186895396764351

theorem tailTrace_530584 : CollatzResearch.WordTrace tailWord_530584 prefixEnd_530584 242172995186895396764351 := by
  unfold tailWord_530584
  simp only [CollatzResearch.WordTrace]
  refine ⟨9675994154896129688979403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12901325539861506251972537 9675994154896129688979403)
  ·
    refine ⟨14513991232344194533469105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9675994154896129688979403 14513991232344194533469105)
    ·
      refine ⟨10885493424258145900101829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14513991232344194533469105 10885493424258145900101829)
      ·
        refine ⟨2041030017048402356269093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10885493424258145900101829 2041030017048402356269093)
        ·
          refine ⟨382693128196575441800455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2041030017048402356269093 382693128196575441800455)
          ·
            refine ⟨574039692294863162700683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382693128196575441800455 574039692294863162700683)
            ·
              refine ⟨861059538442294744051025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574039692294863162700683 861059538442294744051025)
              ·
                refine ⟨645794653831721058038269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 861059538442294744051025 645794653831721058038269)
                ·
                  refine ⟨242172995186895396764351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645794653831721058038269 242172995186895396764351)
                  ·
                    rfl

theorem cell20_530584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 3].length) (baseStart_530584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530584 prefixEnd_530584 := by exact prefixLift 530584
  have htrace : WordTrace (prefixWord ++ tailWord_530584) baseStart_530584 baseEnd_530584 := by
    simpa [prefixWord, tailWord_530584, baseEnd_530584] using wordTrace_append hprefix tailTrace_530584
  have hstable : (prefixWord ++ tailWord_530584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530584).length < 2 ^ (prefixWord ++ tailWord_530584).sum := by decide
  have hdescent : baseEnd_530584 < baseStart_530584 := by decide
  rcases family_descends (prefixWord ++ tailWord_530584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530616 : List Nat := [2, 1, 2, 1, 2, 1, 3, 4, 4]
def baseStart_530616 : Nat := 118140960795 + 530616 * 2 ^ 59
def prefixEnd_530616 : Nat := 4983230072969 + 3 ^ 40 * 530616 * 2
def baseEnd_530616 : Nat := 242187600858845507697553

theorem tailTrace_530616 : CollatzResearch.WordTrace tailWord_530616 prefixEnd_530616 242187600858845507697553 := by
  unfold tailWord_530616
  simp only [CollatzResearch.WordTrace]
  refine ⟨9676577722838164421561851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12902103630450885895415801 9676577722838164421561851)
  ·
    refine ⟨14514866584257246632342777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9676577722838164421561851 14514866584257246632342777)
    ·
      refine ⟨10886149938192934974257083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14514866584257246632342777 10886149938192934974257083)
      ·
        refine ⟨16329224907289402461385625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10886149938192934974257083 16329224907289402461385625)
        ·
          refine ⟨12246918680467051846039219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16329224907289402461385625 12246918680467051846039219)
          ·
            refine ⟨18370378020700577769058829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12246918680467051846039219 18370378020700577769058829)
            ·
              refine ⟨6888891757762716663397061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18370378020700577769058829 6888891757762716663397061)
              ·
                refine ⟨1291667204580509374386949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6888891757762716663397061 1291667204580509374386949)
                ·
                  refine ⟨242187600858845507697553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1291667204580509374386949 242187600858845507697553)
                  ·
                    rfl

theorem cell20_530616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_530616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530616 prefixEnd_530616 := by exact prefixLift 530616
  have htrace : WordTrace (prefixWord ++ tailWord_530616) baseStart_530616 baseEnd_530616 := by
    simpa [prefixWord, tailWord_530616, baseEnd_530616] using wordTrace_append hprefix tailTrace_530616
  have hstable : (prefixWord ++ tailWord_530616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530616).length < 2 ^ (prefixWord ++ tailWord_530616).sum := by decide
  have hdescent : baseEnd_530616 < baseStart_530616 := by decide
  rcases family_descends (prefixWord ++ tailWord_530616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530625 : List Nat := [1, 2, 6, 1, 3, 1, 1, 3, 2]
def baseStart_530625 : Nat := 118140960795 + 530625 * 2 ^ 59
def prefixEnd_530625 : Nat := 4983230072969 + 3 ^ 40 * 530625 * 2
def baseEnd_530625 : Nat := 242191708704081476397517

theorem tailTrace_530625 : CollatzResearch.WordTrace tailWord_530625 prefixEnd_530625 242191708704081476397517 := by
  unfold tailWord_530625
  simp only [CollatzResearch.WordTrace]
  refine ⟨19353483702643723380201329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12902322468429148920134219 19353483702643723380201329)
  ·
    refine ⟨14515112776982792535150997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19353483702643723380201329 14515112776982792535150997)
    ·
      refine ⟨680395911421068400085203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14515112776982792535150997 680395911421068400085203)
      ·
        refine ⟨1020593867131602600127805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680395911421068400085203 1020593867131602600127805)
        ·
          refine ⟨382722700174350975047927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1020593867131602600127805 382722700174350975047927)
          ·
            refine ⟨574084050261526462571891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382722700174350975047927 574084050261526462571891)
            ·
              refine ⟨861126075392289693857837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574084050261526462571891 861126075392289693857837)
              ·
                refine ⟨322922278272108635196689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 861126075392289693857837 322922278272108635196689)
                ·
                  refine ⟨242191708704081476397517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322922278272108635196689 242191708704081476397517)
                  ·
                    rfl

theorem cell20_530625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 2].length) (baseStart_530625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530625 prefixEnd_530625 := by exact prefixLift 530625
  have htrace : WordTrace (prefixWord ++ tailWord_530625) baseStart_530625 baseEnd_530625 := by
    simpa [prefixWord, tailWord_530625, baseEnd_530625] using wordTrace_append hprefix tailTrace_530625
  have hstable : (prefixWord ++ tailWord_530625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530625).length < 2 ^ (prefixWord ++ tailWord_530625).sum := by decide
  have hdescent : baseEnd_530625 < baseStart_530625 := by decide
  rcases family_descends (prefixWord ++ tailWord_530625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530633 : List Nat := [1, 2, 1, 1, 2, 1, 1, 9, 2]
def baseStart_530633 : Nat := 118140960795 + 530633 * 2 ^ 59
def prefixEnd_530633 : Nat := 4983230072969 + 3 ^ 40 * 530633 * 2
def baseEnd_530633 : Nat := 242195360122069004130817

theorem tailTrace_530633 : CollatzResearch.WordTrace tailWord_530633 prefixEnd_530633 242195360122069004130817 := by
  unfold tailWord_530633
  simp only [CollatzResearch.WordTrace]
  refine ⟨19353775486614740746492553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12902516991076493830995035 19353775486614740746492553)
  ·
    refine ⟨14515331614961055559869415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19353775486614740746492553 14515331614961055559869415)
    ·
      refine ⟨21772997422441583339804123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14515331614961055559869415 21772997422441583339804123)
      ·
        refine ⟨32659496133662375009706185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21772997422441583339804123 32659496133662375009706185)
        ·
          refine ⟨24494622100246781257279639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32659496133662375009706185 24494622100246781257279639)
          ·
            refine ⟨36741933150370171885919459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24494622100246781257279639 36741933150370171885919459)
            ·
              refine ⟨55112899725555257828879189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36741933150370171885919459 55112899725555257828879189)
              ·
                refine ⟨322927146829425338841089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 55112899725555257828879189 322927146829425338841089)
                ·
                  refine ⟨242195360122069004130817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322927146829425338841089 242195360122069004130817)
                  ·
                    rfl

theorem cell20_530633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 2].length) (baseStart_530633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530633 prefixEnd_530633 := by exact prefixLift 530633
  have htrace : WordTrace (prefixWord ++ tailWord_530633) baseStart_530633 baseEnd_530633 := by
    simpa [prefixWord, tailWord_530633, baseEnd_530633] using wordTrace_append hprefix tailTrace_530633
  have hstable : (prefixWord ++ tailWord_530633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530633).length < 2 ^ (prefixWord ++ tailWord_530633).sum := by decide
  have hdescent : baseEnd_530633 < baseStart_530633 := by decide
  rcases family_descends (prefixWord ++ tailWord_530633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530636 : List Nat := [2, 2, 1, 6, 2, 1, 6]
def baseStart_530636 : Nat := 118140960795 + 530636 * 2 ^ 59
def prefixEnd_530636 : Nat := 4983230072969 + 3 ^ 40 * 530636 * 2
def baseEnd_530636 : Nat := 26910747711534925225645

theorem tailTrace_530636 : CollatzResearch.WordTrace tailWord_530636 prefixEnd_530636 26910747711534925225645 := by
  unfold tailWord_530636
  simp only [CollatzResearch.WordTrace]
  refine ⟨9676942452801936129425881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12902589937069248172567841 9676942452801936129425881)
  ·
    refine ⟨7257706839601452097069411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9676942452801936129425881 7257706839601452097069411)
    ·
      refine ⟨10886560259402178145604117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7257706839601452097069411 10886560259402178145604117)
      ·
        refine ⟨510307512159477100575193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10886560259402178145604117 510307512159477100575193)
        ·
          refine ⟨382730634119607825431395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510307512159477100575193 382730634119607825431395)
          ·
            refine ⟨574095951179411738147093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382730634119607825431395 574095951179411738147093)
            ·
              refine ⟨26910747711534925225645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 574095951179411738147093 26910747711534925225645)
              ·
                rfl

theorem cell20_530636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 6].length) (baseStart_530636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530636 prefixEnd_530636 := by exact prefixLift 530636
  have htrace : WordTrace (prefixWord ++ tailWord_530636) baseStart_530636 baseEnd_530636 := by
    simpa [prefixWord, tailWord_530636, baseEnd_530636] using wordTrace_append hprefix tailTrace_530636
  have hstable : (prefixWord ++ tailWord_530636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530636).length < 2 ^ (prefixWord ++ tailWord_530636).sum := by decide
  have hdescent : baseEnd_530636 < baseStart_530636 := by decide
  rcases family_descends (prefixWord ++ tailWord_530636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530647 : List Nat := [1, 1, 3, 2, 1, 2, 1, 6, 3]
def baseStart_530647 : Nat := 118140960795 + 530647 * 2 ^ 59
def prefixEnd_530647 : Nat := 4983230072969 + 3 ^ 40 * 530647 * 2
def baseEnd_530647 : Nat := 242201750103547177664093

theorem tailTrace_530647 : CollatzResearch.WordTrace tailWord_530647 prefixEnd_530647 242201750103547177664093 := by
  unfold tailWord_530647
  simp only [CollatzResearch.WordTrace]
  refine ⟨19354286108564021137502195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12902857405709347425001463 19354286108564021137502195)
  ·
    refine ⟨29031429162846031706253293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19354286108564021137502195 29031429162846031706253293)
    ·
      refine ⟨10886785936067261889844985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29031429162846031706253293 10886785936067261889844985)
      ·
        refine ⟨8165089452050446417383739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10886785936067261889844985 8165089452050446417383739)
        ·
          refine ⟨12247634178075669626075609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8165089452050446417383739 12247634178075669626075609)
          ·
            refine ⟨9185725633556752219556707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12247634178075669626075609 9185725633556752219556707)
            ·
              refine ⟨13778588450335128329335061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9185725633556752219556707 13778588450335128329335061)
              ·
                refine ⟨645871333609459140437581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13778588450335128329335061 645871333609459140437581)
                ·
                  refine ⟨242201750103547177664093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645871333609459140437581 242201750103547177664093)
                  ·
                    rfl

theorem cell20_530647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 3].length) (baseStart_530647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530647 prefixEnd_530647 := by exact prefixLift 530647
  have htrace : WordTrace (prefixWord ++ tailWord_530647) baseStart_530647 baseEnd_530647 := by
    simpa [prefixWord, tailWord_530647, baseEnd_530647] using wordTrace_append hprefix tailTrace_530647
  have hstable : (prefixWord ++ tailWord_530647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530647).length < 2 ^ (prefixWord ++ tailWord_530647).sum := by decide
  have hdescent : baseEnd_530647 < baseStart_530647 := by decide
  rcases family_descends (prefixWord ++ tailWord_530647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530664 : List Nat := [2, 1, 4, 1, 2, 3, 1, 3, 3]
def baseStart_530664 : Nat := 118140960795 + 530664 * 2 ^ 59
def prefixEnd_530664 : Nat := 4983230072969 + 3 ^ 40 * 530664 * 2
def baseEnd_530664 : Nat := 242209509366770674097357

theorem tailTrace_530664 : CollatzResearch.WordTrace tailWord_530664 prefixEnd_530664 242209509366770674097357 := by
  unfold tailWord_530664
  simp only [CollatzResearch.WordTrace]
  refine ⟨9677453074751216520435523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12903270766334955360580697 9677453074751216520435523)
  ·
    refine ⟨14516179612126824780653285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9677453074751216520435523 14516179612126824780653285)
    ·
      refine ⟨2721783677273779646372491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14516179612126824780653285 2721783677273779646372491)
      ·
        refine ⟨4082675515910669469558737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2721783677273779646372491 4082675515910669469558737)
        ·
          refine ⟨3062006636933002102169053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4082675515910669469558737 3062006636933002102169053)
          ·
            refine ⟨1148252488849875788313395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3062006636933002102169053 1148252488849875788313395)
            ·
              refine ⟨1722378733274813682470093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148252488849875788313395 1722378733274813682470093)
              ·
                refine ⟨645892024978055130926285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1722378733274813682470093 645892024978055130926285)
                ·
                  refine ⟨242209509366770674097357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645892024978055130926285 242209509366770674097357)
                  ·
                    rfl

theorem cell20_530664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_530664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530664 prefixEnd_530664 := by exact prefixLift 530664
  have htrace : WordTrace (prefixWord ++ tailWord_530664) baseStart_530664 baseEnd_530664 := by
    simpa [prefixWord, tailWord_530664, baseEnd_530664] using wordTrace_append hprefix tailTrace_530664
  have hstable : (prefixWord ++ tailWord_530664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530664).length < 2 ^ (prefixWord ++ tailWord_530664).sum := by decide
  have hdescent : baseEnd_530664 < baseStart_530664 := by decide
  rcases family_descends (prefixWord ++ tailWord_530664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530678 : List Nat := [5, 1, 1, 1, 1, 1, 4, 6]
def baseStart_530678 : Nat := 118140960795 + 530678 * 2 ^ 59
def prefixEnd_530678 : Nat := 4983230072969 + 3 ^ 40 * 530678 * 2
def baseEnd_530678 : Nat := 80738633116082949210211

theorem tailTrace_530678 : CollatzResearch.WordTrace tailWord_530678 prefixEnd_530678 80738633116082949210211 := by
  unfold tailWord_530678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1209713548215732089492543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12903611180967808954587125 1209713548215732089492543)
  ·
    refine ⟨1814570322323598134238815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1209713548215732089492543 1814570322323598134238815)
    ·
      refine ⟨2721855483485397201358223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1814570322323598134238815 2721855483485397201358223)
      ·
        refine ⟨4082783225228095802037335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2721855483485397201358223 4082783225228095802037335)
        ·
          refine ⟨6124174837842143703056003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4082783225228095802037335 6124174837842143703056003)
          ·
            refine ⟨9186262256763215554584005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6124174837842143703056003 9186262256763215554584005)
            ·
              refine ⟨1722424173143102916484501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9186262256763215554584005 1722424173143102916484501)
              ·
                refine ⟨80738633116082949210211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1722424173143102916484501 80738633116082949210211)
                ·
                  rfl

theorem cell20_530678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_530678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530678 prefixEnd_530678 := by exact prefixLift 530678
  have htrace : WordTrace (prefixWord ++ tailWord_530678) baseStart_530678 baseEnd_530678 := by
    simpa [prefixWord, tailWord_530678, baseEnd_530678] using wordTrace_append hprefix tailTrace_530678
  have hstable : (prefixWord ++ tailWord_530678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530678).length < 2 ^ (prefixWord ++ tailWord_530678).sum := by decide
  have hdescent : baseEnd_530678 < baseStart_530678 := by decide
  rcases family_descends (prefixWord ++ tailWord_530678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530695 : List Nat := [1, 1, 4, 5, 2, 7]
def baseStart_530695 : Nat := 118140960795 + 530695 * 2 ^ 59
def prefixEnd_530695 : Nat := 4983230072969 + 3 ^ 40 * 530695 * 2
def baseEnd_530695 : Nat := 8971246615239716446811

theorem tailTrace_530695 : CollatzResearch.WordTrace tailWord_530695 prefixEnd_530695 8971246615239716446811 := by
  unfold tailWord_530695
  simp only [CollatzResearch.WordTrace]
  refine ⟨19356036812390125335249539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12904024541593416890166359 19356036812390125335249539)
  ·
    refine ⟨29034055218585188002874309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19356036812390125335249539 29034055218585188002874309)
    ·
      refine ⟨5443885353484722750538933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29034055218585188002874309 5443885353484722750538933)
      ·
        refine ⟨510364251889192757863025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5443885353484722750538933 510364251889192757863025)
        ·
          refine ⟨382773188916894568397269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510364251889192757863025 382773188916894568397269)
          ·
            refine ⟨8971246615239716446811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 382773188916894568397269 8971246615239716446811)
            ·
              rfl

theorem cell20_530695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 7].length) (baseStart_530695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530695 prefixEnd_530695 := by exact prefixLift 530695
  have htrace : WordTrace (prefixWord ++ tailWord_530695) baseStart_530695 baseEnd_530695 := by
    simpa [prefixWord, tailWord_530695, baseEnd_530695] using wordTrace_append hprefix tailTrace_530695
  have hstable : (prefixWord ++ tailWord_530695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530695).length < 2 ^ (prefixWord ++ tailWord_530695).sum := by decide
  have hdescent : baseEnd_530695 < baseStart_530695 := by decide
  rcases family_descends (prefixWord ++ tailWord_530695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530702 : List Nat := [4, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_530702 : Nat := 118140960795 + 530702 * 2 ^ 59
def prefixEnd_530702 : Nat := 4983230072969 + 3 ^ 40 * 530702 * 2
def baseEnd_530702 : Nat := 242226853602211430830535

theorem tailTrace_530702 : CollatzResearch.WordTrace tailWord_530702 prefixEnd_530702 242226853602211430830535 := by
  unfold tailWord_530702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2419536515420595691344295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12904194748909843687169573 2419536515420595691344295)
  ·
    refine ⟨3629304773130893537016443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2419536515420595691344295 3629304773130893537016443)
    ·
      refine ⟨5443957159696340305524665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3629304773130893537016443 5443957159696340305524665)
      ·
        refine ⟨4082967869772255229143499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5443957159696340305524665 4082967869772255229143499)
        ·
          refine ⟨6124451804658382843715249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4082967869772255229143499 6124451804658382843715249)
          ·
            refine ⟨4593338853493787132786437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6124451804658382843715249 4593338853493787132786437)
            ·
              refine ⟨861251035030085087397457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4593338853493787132786437 861251035030085087397457)
              ·
                refine ⟨645938276272563815548093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 861251035030085087397457 645938276272563815548093)
                ·
                  refine ⟨242226853602211430830535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645938276272563815548093 242226853602211430830535)
                  ·
                    rfl

theorem cell20_530702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_530702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530702 prefixEnd_530702 := by exact prefixLift 530702
  have htrace : WordTrace (prefixWord ++ tailWord_530702) baseStart_530702 baseEnd_530702 := by
    simpa [prefixWord, tailWord_530702, baseEnd_530702] using wordTrace_append hprefix tailTrace_530702
  have hstable : (prefixWord ++ tailWord_530702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530702).length < 2 ^ (prefixWord ++ tailWord_530702).sum := by decide
  have hdescent : baseEnd_530702 < baseStart_530702 := by decide
  rcases family_descends (prefixWord ++ tailWord_530702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530705 : List Nat := [1, 2, 2, 1, 1, 7, 2, 2, 2]
def baseStart_530705 : Nat := 118140960795 + 530705 * 2 ^ 59
def prefixEnd_530705 : Nat := 4983230072969 + 3 ^ 40 * 530705 * 2
def baseEnd_530705 : Nat := 242228222883956753730523

theorem tailTrace_530705 : CollatzResearch.WordTrace tailWord_530705 prefixEnd_530705 242228222883956753730523 := by
  unfold tailWord_530705
  simp only [CollatzResearch.WordTrace]
  refine ⟨19356401542353897043113569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12904267694902598028742379 19356401542353897043113569)
  ·
    refine ⟨14517301156765422782335177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19356401542353897043113569 14517301156765422782335177)
    ·
      refine ⟨10887975867574067086751383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14517301156765422782335177 10887975867574067086751383)
      ·
        refine ⟨16331963801361100630127075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10887975867574067086751383 16331963801361100630127075)
        ·
          refine ⟨24497945702041650945190613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16331963801361100630127075 24497945702041650945190613)
          ·
            refine ⟨574170602391601194027905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 24497945702041650945190613 574170602391601194027905)
            ·
              refine ⟨430627951793700895520929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574170602391601194027905 430627951793700895520929)
              ·
                refine ⟨322970963845275671640697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430627951793700895520929 322970963845275671640697)
                ·
                  refine ⟨242228222883956753730523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322970963845275671640697 242228222883956753730523)
                  ·
                    rfl

theorem cell20_530705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 2].length) (baseStart_530705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530705 prefixEnd_530705 := by exact prefixLift 530705
  have htrace : WordTrace (prefixWord ++ tailWord_530705) baseStart_530705 baseEnd_530705 := by
    simpa [prefixWord, tailWord_530705, baseEnd_530705] using wordTrace_append hprefix tailTrace_530705
  have hstable : (prefixWord ++ tailWord_530705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530705).length < 2 ^ (prefixWord ++ tailWord_530705).sum := by decide
  have hdescent : baseEnd_530705 < baseStart_530705 := by decide
  rcases family_descends (prefixWord ++ tailWord_530705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530723 : List Nat := [1, 1, 1, 4, 2, 2, 1, 5, 3]
def baseStart_530723 : Nat := 118140960795 + 530723 * 2 ^ 59
def prefixEnd_530723 : Nat := 4983230072969 + 3 ^ 40 * 530723 * 2
def baseEnd_530723 : Nat := 242236438574428691130449

theorem tailTrace_530723 : CollatzResearch.WordTrace tailWord_530723 prefixEnd_530723 242236438574428691130449 := by
  unfold tailWord_530723
  simp only [CollatzResearch.WordTrace]
  refine ⟨19357058056288686117268823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12904705370859124078179215 19357058056288686117268823)
  ·
    refine ⟨29035587084433029175903235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19357058056288686117268823 29035587084433029175903235)
    ·
      refine ⟨43553380626649543763854853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29035587084433029175903235 43553380626649543763854853)
      ·
        refine ⟨8166258867496789455722785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43553380626649543763854853 8166258867496789455722785)
        ·
          refine ⟨6124694150622592091792089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8166258867496789455722785 6124694150622592091792089)
          ·
            refine ⟨4593520612966944068844067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6124694150622592091792089 4593520612966944068844067)
            ·
              refine ⟨6890280919450416103266101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4593520612966944068844067 6890280919450416103266101)
              ·
                refine ⟨645963836198476509681197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6890280919450416103266101 645963836198476509681197)
                ·
                  refine ⟨242236438574428691130449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645963836198476509681197 242236438574428691130449)
                  ·
                    rfl

theorem cell20_530723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 3].length) (baseStart_530723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530723 prefixEnd_530723 := by exact prefixLift 530723
  have htrace : WordTrace (prefixWord ++ tailWord_530723) baseStart_530723 baseEnd_530723 := by
    simpa [prefixWord, tailWord_530723, baseEnd_530723] using wordTrace_append hprefix tailTrace_530723
  have hstable : (prefixWord ++ tailWord_530723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530723).length < 2 ^ (prefixWord ++ tailWord_530723).sum := by decide
  have hdescent : baseEnd_530723 < baseStart_530723 := by decide
  rcases family_descends (prefixWord ++ tailWord_530723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530768 : List Nat := [2, 1, 1, 1, 1, 6, 1, 3, 4]
def baseStart_530768 : Nat := 118140960795 + 530768 * 2 ^ 59
def prefixEnd_530768 : Nat := 4983230072969 + 3 ^ 40 * 530768 * 2
def baseEnd_530768 : Nat := 242256977800608534630265

theorem tailTrace_530768 : CollatzResearch.WordTrace tailWord_530768 prefixEnd_530768 242256977800608534630265 := by
  unfold tailWord_530768
  simp only [CollatzResearch.WordTrace]
  refine ⟨9679349670562829401328479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12905799560750439201771305 9679349670562829401328479)
  ·
    refine ⟨14519024505844244101992719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9679349670562829401328479 14519024505844244101992719)
    ·
      refine ⟨21778536758766366152989079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14519024505844244101992719 21778536758766366152989079)
      ·
        refine ⟨32667805138149549229483619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21778536758766366152989079 32667805138149549229483619)
        ·
          refine ⟨49001707707224323844225429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32667805138149549229483619 49001707707224323844225429)
          ·
            refine ⟨2296955048776140180198067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49001707707224323844225429 2296955048776140180198067)
            ·
              refine ⟨3445432573164210270297101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2296955048776140180198067 3445432573164210270297101)
              ·
                refine ⟨1292037214936578851361413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3445432573164210270297101 1292037214936578851361413)
                ·
                  refine ⟨242256977800608534630265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1292037214936578851361413 242256977800608534630265)
                  ·
                    rfl

theorem cell20_530768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_530768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530768 prefixEnd_530768 := by exact prefixLift 530768
  have htrace : WordTrace (prefixWord ++ tailWord_530768) baseStart_530768 baseEnd_530768 := by
    simpa [prefixWord, tailWord_530768, baseEnd_530768] using wordTrace_append hprefix tailTrace_530768
  have hstable : (prefixWord ++ tailWord_530768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530768).length < 2 ^ (prefixWord ++ tailWord_530768).sum := by decide
  have hdescent : baseEnd_530768 < baseStart_530768 := by decide
  rcases family_descends (prefixWord ++ tailWord_530768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530775 : List Nat := [1, 1, 3, 2, 3, 1, 2, 7]
def baseStart_530775 : Nat := 118140960795 + 530775 * 2 ^ 59
def prefixEnd_530775 : Nat := 4983230072969 + 3 ^ 40 * 530775 * 2
def baseEnd_530775 : Nat := 80753390930449207132301

theorem tailTrace_530775 : CollatzResearch.WordTrace tailWord_530775 prefixEnd_530775 80753390930449207132301 := by
  unfold tailWord_530775
  simp only [CollatzResearch.WordTrace]
  refine ⟨19358954652100298998161779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12905969768066865998774519 19358954652100298998161779)
  ·
    refine ⟨29038431978150448497242669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19358954652100298998161779 29038431978150448497242669)
    ·
      refine ⟨10889411991806418186466001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29038431978150448497242669 10889411991806418186466001)
      ·
        refine ⟨8167058993854813639849501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10889411991806418186466001 8167058993854813639849501)
        ·
          refine ⟨3062647122695555114943563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8167058993854813639849501 3062647122695555114943563)
          ·
            refine ⟨4593970684043332672415345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3062647122695555114943563 4593970684043332672415345)
            ·
              refine ⟨3445478013032499504311509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4593970684043332672415345 3445478013032499504311509)
              ·
                refine ⟨80753390930449207132301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3445478013032499504311509 80753390930449207132301)
                ·
                  rfl

theorem cell20_530775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 7].length) (baseStart_530775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530775 prefixEnd_530775 := by exact prefixLift 530775
  have htrace : WordTrace (prefixWord ++ tailWord_530775) baseStart_530775 baseEnd_530775 := by
    simpa [prefixWord, tailWord_530775, baseEnd_530775] using wordTrace_append hprefix tailTrace_530775
  have hstable : (prefixWord ++ tailWord_530775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530775).length < 2 ^ (prefixWord ++ tailWord_530775).sum := by decide
  have hdescent : baseEnd_530775 < baseStart_530775 := by decide
  rcases family_descends (prefixWord ++ tailWord_530775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530792 : List Nat := [2, 1, 4, 2, 2, 2, 1, 6]
def baseStart_530792 : Nat := 118140960795 + 530792 * 2 ^ 59
def prefixEnd_530792 : Nat := 4983230072969 + 3 ^ 40 * 530792 * 2
def baseEnd_530792 : Nat := 80755977351523705943389

theorem tailTrace_530792 : CollatzResearch.WordTrace tailWord_530792 prefixEnd_530792 80755977351523705943389 := by
  unfold tailWord_530792
  simp only [CollatzResearch.WordTrace]
  refine ⟨9679787346519355450765315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12906383128692473934353753 9679787346519355450765315)
  ·
    refine ⟨14519681019779033176147973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9679787346519355450765315 14519681019779033176147973)
    ·
      refine ⟨2722440191208568720527745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14519681019779033176147973 2722440191208568720527745)
      ·
        refine ⟨2041830143406426540395809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2722440191208568720527745 2041830143406426540395809)
        ·
          refine ⟨1531372607554819905296857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2041830143406426540395809 1531372607554819905296857)
          ·
            refine ⟨1148529455666114928972643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1531372607554819905296857 1148529455666114928972643)
            ·
              refine ⟨1722794183499172393458965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148529455666114928972643 1722794183499172393458965)
              ·
                refine ⟨80755977351523705943389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1722794183499172393458965 80755977351523705943389)
                ·
                  rfl

theorem cell20_530792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_530792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530792 prefixEnd_530792 := by exact prefixLift 530792
  have htrace : WordTrace (prefixWord ++ tailWord_530792) baseStart_530792 baseEnd_530792 := by
    simpa [prefixWord, tailWord_530792, baseEnd_530792] using wordTrace_append hprefix tailTrace_530792
  have hstable : (prefixWord ++ tailWord_530792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530792).length < 2 ^ (prefixWord ++ tailWord_530792).sum := by decide
  have hdescent : baseEnd_530792 < baseStart_530792 := by decide
  rcases family_descends (prefixWord ++ tailWord_530792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530802 : List Nat := [3, 2, 1, 2, 1, 3, 3, 3, 2]
def baseStart_530802 : Nat := 118140960795 + 530802 * 2 ^ 59
def prefixEnd_530802 : Nat := 4983230072969 + 3 ^ 40 * 530802 * 2
def baseEnd_530802 : Nat := 242272496327055527496793

theorem tailTrace_530802 : CollatzResearch.WordTrace tailWord_530802 prefixEnd_530802 242272496327055527496793 := by
  unfold tailWord_530802
  simp only [CollatzResearch.WordTrace]
  refine ⟨4839984855750620652348665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12906626282001655072929773 4839984855750620652348665)
  ·
    refine ⟨3629988641812965489261499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4839984855750620652348665 3629988641812965489261499)
    ·
      refine ⟨5444982962719448233892249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3629988641812965489261499 5444982962719448233892249)
      ·
        refine ⟨4083737222039586175419187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5444982962719448233892249 4083737222039586175419187)
        ·
          refine ⟨6125605833059379263128781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4083737222039586175419187 6125605833059379263128781)
          ·
            refine ⟨2297102187397267223673293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6125605833059379263128781 2297102187397267223673293)
            ·
              refine ⟨861413320273975208877485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2297102187397267223673293 861413320273975208877485)
              ·
                refine ⟨323029995102740703329057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 861413320273975208877485 323029995102740703329057)
                ·
                  refine ⟨242272496327055527496793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323029995102740703329057 242272496327055527496793)
                  ·
                    rfl

theorem cell20_530802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_530802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530802 prefixEnd_530802 := by exact prefixLift 530802
  have htrace : WordTrace (prefixWord ++ tailWord_530802) baseStart_530802 baseEnd_530802 := by
    simpa [prefixWord, tailWord_530802, baseEnd_530802] using wordTrace_append hprefix tailTrace_530802
  have hstable : (prefixWord ++ tailWord_530802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530802).length < 2 ^ (prefixWord ++ tailWord_530802).sum := by decide
  have hdescent : baseEnd_530802 < baseStart_530802 := by decide
  rcases family_descends (prefixWord ++ tailWord_530802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530813 : List Nat := [1, 4, 1, 1, 2, 3, 8]
def baseStart_530813 : Nat := 118140960795 + 530813 * 2 ^ 59
def prefixEnd_530813 : Nat := 4983230072969 + 3 ^ 40 * 530813 * 2
def baseEnd_530813 : Nat := 26919724114087597570009

theorem tailTrace_530813 : CollatzResearch.WordTrace tailWord_530813 prefixEnd_530813 26919724114087597570009 := by
  unfold tailWord_530813
  simp only [CollatzResearch.WordTrace]
  refine ⟨19360340625962631488045093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12906893750641754325363395 19360340625962631488045093)
  ·
    refine ⟨3630063867367993404008455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19360340625962631488045093 3630063867367993404008455)
    ·
      refine ⟨5445095801051990106012683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3630063867367993404008455 5445095801051990106012683)
      ·
        refine ⟨8167643701577985159019025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5445095801051990106012683 8167643701577985159019025)
        ·
          refine ⟨6125732776183488869264269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8167643701577985159019025 6125732776183488869264269)
          ·
            refine ⟨2297149791068808325974101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6125732776183488869264269 2297149791068808325974101)
            ·
              refine ⟨26919724114087597570009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2297149791068808325974101 26919724114087597570009)
              ·
                rfl

theorem cell20_530813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 8].length) (baseStart_530813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530813 prefixEnd_530813 := by exact prefixLift 530813
  have htrace : WordTrace (prefixWord ++ tailWord_530813) baseStart_530813 baseEnd_530813 := by
    simpa [prefixWord, tailWord_530813, baseEnd_530813] using wordTrace_append hprefix tailTrace_530813
  have hstable : (prefixWord ++ tailWord_530813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530813).length < 2 ^ (prefixWord ++ tailWord_530813).sum := by decide
  have hdescent : baseEnd_530813 < baseStart_530813 := by decide
  rcases family_descends (prefixWord ++ tailWord_530813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530819 : List Nat := [1, 1, 1, 3, 6, 1, 3, 2, 2]
def baseStart_530819 : Nat := 118140960795 + 530819 * 2 ^ 59
def prefixEnd_530819 : Nat := 4983230072969 + 3 ^ 40 * 530819 * 2
def baseEnd_530819 : Nat := 242280255590279023930057

theorem tailTrace_530819 : CollatzResearch.WordTrace tailWord_530819 prefixEnd_530819 242280255590279023930057 := by
  unfold tailWord_530819
  simp only [CollatzResearch.WordTrace]
  refine ⟨19360559463940894512763511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12907039642627263008509007 19360559463940894512763511)
  ·
    refine ⟨29040839195911341769145267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19360559463940894512763511 29040839195911341769145267)
    ·
      refine ⟨43561258793867012653717901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29040839195911341769145267 43561258793867012653717901)
      ·
        refine ⟨16335472047700129745144213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43561258793867012653717901 16335472047700129745144213)
        ·
          refine ⟨765725252235943581803635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16335472047700129745144213 765725252235943581803635)
          ·
            refine ⟨1148587878353915372705453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765725252235943581803635 1148587878353915372705453)
            ·
              refine ⟨430720454382718264764545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1148587878353915372705453 430720454382718264764545)
              ·
                refine ⟨323040340787038698573409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430720454382718264764545 323040340787038698573409)
                ·
                  refine ⟨242280255590279023930057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323040340787038698573409 242280255590279023930057)
                  ·
                    rfl

theorem cell20_530819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 2].length) (baseStart_530819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530819 prefixEnd_530819 := by exact prefixLift 530819
  have htrace : WordTrace (prefixWord ++ tailWord_530819) baseStart_530819 baseEnd_530819 := by
    simpa [prefixWord, tailWord_530819, baseEnd_530819] using wordTrace_append hprefix tailTrace_530819
  have hstable : (prefixWord ++ tailWord_530819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530819).length < 2 ^ (prefixWord ++ tailWord_530819).sum := by decide
  have hdescent : baseEnd_530819 < baseStart_530819 := by decide
  rcases family_descends (prefixWord ++ tailWord_530819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530830 : List Nat := [4, 1, 1, 4, 1, 1, 1, 7]
def baseStart_530830 : Nat := 118140960795 + 530830 * 2 ^ 59
def prefixEnd_530830 : Nat := 4983230072969 + 3 ^ 40 * 530830 * 2
def baseEnd_530830 : Nat := 80761758763337291521115

theorem tailTrace_530830 : CollatzResearch.WordTrace tailWord_530830 prefixEnd_530830 80761758763337291521115 := by
  unfold tailWord_530830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2420120083362630423926743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12907307111267362260942629 2420120083362630423926743)
  ·
    refine ⟨3630180125043945635890115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2420120083362630423926743 3630180125043945635890115)
    ·
      refine ⟨5445270187565918453835173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3630180125043945635890115 5445270187565918453835173)
      ·
        refine ⟨1020988160168609710094095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5445270187565918453835173 1020988160168609710094095)
        ·
          refine ⟨1531482240252914565141143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020988160168609710094095 1531482240252914565141143)
          ·
            refine ⟨2297223360379371847711715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1531482240252914565141143 2297223360379371847711715)
            ·
              refine ⟨3445835040569057771567573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2297223360379371847711715 3445835040569057771567573)
              ·
                refine ⟨80761758763337291521115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3445835040569057771567573 80761758763337291521115)
                ·
                  rfl

theorem cell20_530830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_530830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530830 prefixEnd_530830 := by exact prefixLift 530830
  have htrace : WordTrace (prefixWord ++ tailWord_530830) baseStart_530830 baseEnd_530830 := by
    simpa [prefixWord, tailWord_530830, baseEnd_530830] using wordTrace_append hprefix tailTrace_530830
  have hstable : (prefixWord ++ tailWord_530830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530830).length < 2 ^ (prefixWord ++ tailWord_530830).sum := by decide
  have hdescent : baseEnd_530830 < baseStart_530830 := by decide
  rcases family_descends (prefixWord ++ tailWord_530830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530851 : List Nat := [1, 1, 1, 4, 1, 4, 2, 6]
def baseStart_530851 : Nat := 118140960795 + 530851 * 2 ^ 59
def prefixEnd_530851 : Nat := 4983230072969 + 3 ^ 40 * 530851 * 2
def baseEnd_530851 : Nat := 80764953754076378287753

theorem tailTrace_530851 : CollatzResearch.WordTrace tailWord_530851 prefixEnd_530851 80764953754076378287753 := by
  unfold tailWord_530851
  simp only [CollatzResearch.WordTrace]
  refine ⟨19361726599824963977928407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12907817733216642651952271 19361726599824963977928407)
  ·
    refine ⟨29042589899737445966892611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19361726599824963977928407 29042589899737445966892611)
    ·
      refine ⟨43563884849606168950338917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29042589899737445966892611 43563884849606168950338917)
      ·
        refine ⟨8168228409301156678188547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43563884849606168950338917 8168228409301156678188547)
        ·
          refine ⟨12252342613951735017282821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8168228409301156678188547 12252342613951735017282821)
          ·
            refine ⟨2297314240115950315740529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12252342613951735017282821 2297314240115950315740529)
            ·
              refine ⟨1722985680086962736805397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2297314240115950315740529 1722985680086962736805397)
              ·
                refine ⟨80764953754076378287753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1722985680086962736805397 80764953754076378287753)
                ·
                  rfl

theorem cell20_530851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 6].length) (baseStart_530851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530851 prefixEnd_530851 := by exact prefixLift 530851
  have htrace : WordTrace (prefixWord ++ tailWord_530851) baseStart_530851 baseEnd_530851 := by
    simpa [prefixWord, tailWord_530851, baseEnd_530851] using wordTrace_append hprefix tailTrace_530851
  have hstable : (prefixWord ++ tailWord_530851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530851).length < 2 ^ (prefixWord ++ tailWord_530851).sum := by decide
  have hdescent : baseEnd_530851 < baseStart_530851 := by decide
  rcases family_descends (prefixWord ++ tailWord_530851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530881 : List Nat := [1, 2, 7, 1, 1, 2, 1, 5]
def baseStart_530881 : Nat := 118140960795 + 530881 * 2 ^ 59
def prefixEnd_530881 : Nat := 4983230072969 + 3 ^ 40 * 530881 * 2
def baseEnd_530881 : Nat := 80769518026560787954379

theorem tailTrace_530881 : CollatzResearch.WordTrace tailWord_530881 prefixEnd_530881 80769518026560787954379 := by
  unfold tailWord_530881
  simp only [CollatzResearch.WordTrace]
  refine ⟨19362820789716279101520497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12908547193144186067680331 19362820789716279101520497)
  ·
    refine ⟨14522115592287209326140373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19362820789716279101520497 14522115592287209326140373)
    ·
      refine ⟨340362084194231468581415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 14522115592287209326140373 340362084194231468581415)
      ·
        refine ⟨510543126291347202872123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340362084194231468581415 510543126291347202872123)
        ·
          refine ⟨765814689437020804308185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510543126291347202872123 765814689437020804308185)
          ·
            refine ⟨574361017077765603231139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765814689437020804308185 574361017077765603231139)
            ·
              refine ⟨861541525616648404846709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574361017077765603231139 861541525616648404846709)
              ·
                refine ⟨80769518026560787954379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 861541525616648404846709 80769518026560787954379)
                ·
                  rfl

theorem cell20_530881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 5].length) (baseStart_530881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530881 prefixEnd_530881 := by exact prefixLift 530881
  have htrace : WordTrace (prefixWord ++ tailWord_530881) baseStart_530881 baseEnd_530881 := by
    simpa [prefixWord, tailWord_530881, baseEnd_530881] using wordTrace_append hprefix tailTrace_530881
  have hstable : (prefixWord ++ tailWord_530881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530881).length < 2 ^ (prefixWord ++ tailWord_530881).sum := by decide
  have hdescent : baseEnd_530881 < baseStart_530881 := by decide
  rcases family_descends (prefixWord ++ tailWord_530881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530889 : List Nat := [1, 2, 1, 1, 2, 1, 7, 5]
def baseStart_530889 : Nat := 118140960795 + 530889 * 2 ^ 59
def prefixEnd_530889 : Nat := 4983230072969 + 3 ^ 40 * 530889 * 2
def baseEnd_530889 : Nat := 80770735165889963865479

theorem tailTrace_530889 : CollatzResearch.WordTrace tailWord_530889 prefixEnd_530889 80770735165889963865479 := by
  unfold tailWord_530889
  simp only [CollatzResearch.WordTrace]
  refine ⟨19363112573687296467811721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12908741715791530978541147 19363112573687296467811721)
  ·
    refine ⟨14522334430265472350858791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19363112573687296467811721 14522334430265472350858791)
    ·
      refine ⟨21783501645398208526288187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14522334430265472350858791 21783501645398208526288187)
      ·
        refine ⟨32675252468097312789432281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21783501645398208526288187 32675252468097312789432281)
        ·
          refine ⟨24506439351072984592074211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32675252468097312789432281 24506439351072984592074211)
          ·
            refine ⟨36759659026609476888111317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24506439351072984592074211 36759659026609476888111317)
            ·
              refine ⟨861554508436159614565109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 36759659026609476888111317 861554508436159614565109)
              ·
                refine ⟨80770735165889963865479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 861554508436159614565109 80770735165889963865479)
                ·
                  rfl

theorem cell20_530889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 5].length) (baseStart_530889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530889 prefixEnd_530889 := by exact prefixLift 530889
  have htrace : WordTrace (prefixWord ++ tailWord_530889) baseStart_530889 baseEnd_530889 := by
    simpa [prefixWord, tailWord_530889, baseEnd_530889] using wordTrace_append hprefix tailTrace_530889
  have hstable : (prefixWord ++ tailWord_530889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530889).length < 2 ^ (prefixWord ++ tailWord_530889).sum := by decide
  have hdescent : baseEnd_530889 < baseStart_530889 := by decide
  rcases family_descends (prefixWord ++ tailWord_530889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530906 : List Nat := [3, 1, 1, 2, 3, 1, 5, 4]
def baseStart_530906 : Nat := 118140960795 + 530906 * 2 ^ 59
def prefixEnd_530906 : Nat := 4983230072969 + 3 ^ 40 * 530906 * 2
def baseEnd_530906 : Nat := 80773321586964462676567

theorem tailTrace_530906 : CollatzResearch.WordTrace tailWord_530906 prefixEnd_530906 80773321586964462676567 := by
  unfold tailWord_530906
  simp only [CollatzResearch.WordTrace]
  refine ⟨4840933153656427092795143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12909155076417138914120381 4840933153656427092795143)
  ·
    refine ⟨7261399730484640639192715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4840933153656427092795143 7261399730484640639192715)
    ·
      refine ⟨10892099595726960958789073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7261399730484640639192715 10892099595726960958789073)
      ·
        refine ⟨8169074696795220719091805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10892099595726960958789073 8169074696795220719091805)
        ·
          refine ⟨3063403011298207769659427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8169074696795220719091805 3063403011298207769659427)
          ·
            refine ⟨4595104516947311654489141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3063403011298207769659427 4595104516947311654489141)
            ·
              refine ⟨430791048463810467608357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4595104516947311654489141 430791048463810467608357)
              ·
                refine ⟨80773321586964462676567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 430791048463810467608357 80773321586964462676567)
                ·
                  rfl

theorem cell20_530906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_530906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530906 prefixEnd_530906 := by exact prefixLift 530906
  have htrace : WordTrace (prefixWord ++ tailWord_530906) baseStart_530906 baseEnd_530906 := by
    simpa [prefixWord, tailWord_530906, baseEnd_530906] using wordTrace_append hprefix tailTrace_530906
  have hstable : (prefixWord ++ tailWord_530906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530906).length < 2 ^ (prefixWord ++ tailWord_530906).sum := by decide
  have hdescent : baseEnd_530906 < baseStart_530906 := by decide
  rcases family_descends (prefixWord ++ tailWord_530906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530930 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 5]
def baseStart_530930 : Nat := 118140960795 + 530930 * 2 ^ 59
def prefixEnd_530930 : Nat := 4983230072969 + 3 ^ 40 * 530930 * 2
def baseEnd_530930 : Nat := 242330919014855971229603

theorem tailTrace_530930 : CollatzResearch.WordTrace tailWord_530930 prefixEnd_530930 242330919014855971229603 := by
  unfold tailWord_530930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4841151991634690117513561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12909738644359173646702829 4841151991634690117513561)
  ·
    refine ⟨3630863993726017588135171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4841151991634690117513561 3630863993726017588135171)
    ·
      refine ⟨5446295990589026382202757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3630863993726017588135171 5446295990589026382202757)
      ·
        refine ⟨1021180498235442446663017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5446295990589026382202757 1021180498235442446663017)
        ·
          refine ⟨765885373676581834997263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1021180498235442446663017 765885373676581834997263)
          ·
            refine ⟨1148828060514872752495895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765885373676581834997263 1148828060514872752495895)
            ·
              refine ⟨1723242090772309128743843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148828060514872752495895 1723242090772309128743843)
              ·
                refine ⟨2584863136158463693115765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723242090772309128743843 2584863136158463693115765)
                ·
                  refine ⟨242330919014855971229603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2584863136158463693115765 242330919014855971229603)
                  ·
                    rfl

theorem cell20_530930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_530930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530930 prefixEnd_530930 := by exact prefixLift 530930
  have htrace : WordTrace (prefixWord ++ tailWord_530930) baseStart_530930 baseEnd_530930 := by
    simpa [prefixWord, tailWord_530930, baseEnd_530930] using wordTrace_append hprefix tailTrace_530930
  have hstable : (prefixWord ++ tailWord_530930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530930).length < 2 ^ (prefixWord ++ tailWord_530930).sum := by decide
  have hdescent : baseEnd_530930 < baseStart_530930 := by decide
  rcases family_descends (prefixWord ++ tailWord_530930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530937 : List Nat := [1, 2, 1, 3, 1, 2, 4, 4, 2]
def baseStart_530937 : Nat := 118140960795 + 530937 * 2 ^ 59
def prefixEnd_530937 : Nat := 4983230072969 + 3 ^ 40 * 530937 * 2
def baseEnd_530937 : Nat := 242334114005595057996241

theorem tailTrace_530937 : CollatzResearch.WordTrace tailWord_530937 prefixEnd_530937 242334114005595057996241 := by
  unfold tailWord_530937
  simp only [CollatzResearch.WordTrace]
  refine ⟨19364863277513400665559065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12909908851675600443706043 19364863277513400665559065)
  ·
    refine ⟨14523647458135050499169299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19364863277513400665559065 14523647458135050499169299)
    ·
      refine ⟨21785471187202575748753949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14523647458135050499169299 21785471187202575748753949)
      ·
        refine ⟨8169551695200965905782731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21785471187202575748753949 8169551695200965905782731)
        ·
          refine ⟨12254327542801448858674097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8169551695200965905782731 12254327542801448858674097)
          ·
            refine ⟨9190745657101086644005573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12254327542801448858674097 9190745657101086644005573)
            ·
              refine ⟨1723264810706453745751045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9190745657101086644005573 1723264810706453745751045)
              ·
                refine ⟨323112152007460077328321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1723264810706453745751045 323112152007460077328321)
                ·
                  refine ⟨242334114005595057996241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323112152007460077328321 242334114005595057996241)
                  ·
                    rfl

theorem cell20_530937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 2].length) (baseStart_530937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530937 prefixEnd_530937 := by exact prefixLift 530937
  have htrace : WordTrace (prefixWord ++ tailWord_530937) baseStart_530937 baseEnd_530937 := by
    simpa [prefixWord, tailWord_530937, baseEnd_530937] using wordTrace_append hprefix tailTrace_530937
  have hstable : (prefixWord ++ tailWord_530937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530937).length < 2 ^ (prefixWord ++ tailWord_530937).sum := by decide
  have hdescent : baseEnd_530937 < baseStart_530937 := by decide
  rcases family_descends (prefixWord ++ tailWord_530937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530957 : List Nat := [1, 7, 1, 1, 1, 3, 2, 4]
def baseStart_530957 : Nat := 118140960795 + 530957 * 2 ^ 59
def prefixEnd_530957 : Nat := 4983230072969 + 3 ^ 40 * 530957 * 2
def baseEnd_530957 : Nat := 80781080850187959109831

theorem tailTrace_530957 : CollatzResearch.WordTrace tailWord_530957 prefixEnd_530957 80781080850187959109831 := by
  unfold tailWord_530957
  simp only [CollatzResearch.WordTrace]
  refine ⟨19365592737440944081287125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12910395158293962720858083 19365592737440944081287125)
  ·
    refine ⟨453881079783772126905167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 19365592737440944081287125 453881079783772126905167)
    ·
      refine ⟨680821619675658190357751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453881079783772126905167 680821619675658190357751)
      ·
        refine ⟨1021232429513487285536627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680821619675658190357751 1021232429513487285536627)
        ·
          refine ⟨1531848644270230928304941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021232429513487285536627 1531848644270230928304941)
          ·
            refine ⟨574443241601336598114353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1531848644270230928304941 574443241601336598114353)
            ·
              refine ⟨430832431201002448585765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574443241601336598114353 430832431201002448585765)
              ·
                refine ⟨80781080850187959109831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 430832431201002448585765 80781080850187959109831)
                ·
                  rfl

theorem cell20_530957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 4].length) (baseStart_530957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530957 prefixEnd_530957 := by exact prefixLift 530957
  have htrace : WordTrace (prefixWord ++ tailWord_530957) baseStart_530957 baseEnd_530957 := by
    simpa [prefixWord, tailWord_530957, baseEnd_530957] using wordTrace_append hprefix tailTrace_530957
  have hstable : (prefixWord ++ tailWord_530957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530957).length < 2 ^ (prefixWord ++ tailWord_530957).sum := by decide
  have hdescent : baseEnd_530957 < baseStart_530957 := by decide
  rcases family_descends (prefixWord ++ tailWord_530957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530965 : List Nat := [1, 3, 2, 1, 3, 1, 3, 6]
def baseStart_530965 : Nat := 118140960795 + 530965 * 2 ^ 59
def prefixEnd_530965 : Nat := 4983230072969 + 3 ^ 40 * 530965 * 2
def baseEnd_530965 : Nat := 80782297989517135020931

theorem tailTrace_530965 : CollatzResearch.WordTrace tailWord_530965 prefixEnd_530965 80782297989517135020931 := by
  unfold tailWord_530965
  simp only [CollatzResearch.WordTrace]
  refine ⟨19365884521411961447578349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12910589680941307631718899 19365884521411961447578349)
  ·
    refine ⟨7262206695529485542841881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19365884521411961447578349 7262206695529485542841881)
    ·
      refine ⟨5446655021647114157131411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7262206695529485542841881 5446655021647114157131411)
      ·
        refine ⟨8169982532470671235697117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5446655021647114157131411 8169982532470671235697117)
        ·
          refine ⟨3063743449676501713386419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8169982532470671235697117 3063743449676501713386419)
          ·
            refine ⟨4595615174514752570079629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3063743449676501713386419 4595615174514752570079629)
            ·
              refine ⟨1723355690443032213779861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4595615174514752570079629 1723355690443032213779861)
              ·
                refine ⟨80782297989517135020931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1723355690443032213779861 80782297989517135020931)
                ·
                  rfl

theorem cell20_530965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 6].length) (baseStart_530965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_530965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_530965 prefixEnd_530965 := by exact prefixLift 530965
  have htrace : WordTrace (prefixWord ++ tailWord_530965) baseStart_530965 baseEnd_530965 := by
    simpa [prefixWord, tailWord_530965, baseEnd_530965] using wordTrace_append hprefix tailTrace_530965
  have hstable : (prefixWord ++ tailWord_530965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530965).length < 2 ^ (prefixWord ++ tailWord_530965).sum := by decide
  have hdescent : baseEnd_530965 < baseStart_530965 := by decide
  rcases family_descends (prefixWord ++ tailWord_530965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531065 : List Nat := [1, 2, 1, 3, 3, 2, 2, 3, 3]
def baseStart_531065 : Nat := 118140960795 + 531065 * 2 ^ 59
def prefixEnd_531065 : Nat := 4983230072969 + 3 ^ 40 * 531065 * 2
def baseEnd_531065 : Nat := 242392536693395501729051

theorem tailTrace_531065 : CollatzResearch.WordTrace tailWord_531065 prefixEnd_531065 242392536693395501729051 := by
  unfold tailWord_531065
  simp only [CollatzResearch.WordTrace]
  refine ⟨19369531821049678526218649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12913021214033119017479099 19369531821049678526218649)
  ·
    refine ⟨14527148865787258894663987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19369531821049678526218649 14527148865787258894663987)
    ·
      refine ⟨21790723298680888341995981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14527148865787258894663987 21790723298680888341995981)
      ·
        refine ⟨8171521237005333128248493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21790723298680888341995981 8171521237005333128248493)
        ·
          refine ⟨3064320463876999923093185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8171521237005333128248493 3064320463876999923093185)
          ·
            refine ⟨2298240347907749942319889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3064320463876999923093185 2298240347907749942319889)
            ·
              refine ⟨1723680260930812456739917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2298240347907749942319889 1723680260930812456739917)
              ·
                refine ⟨646380097849054671277469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1723680260930812456739917 646380097849054671277469)
                ·
                  refine ⟨242392536693395501729051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 646380097849054671277469 242392536693395501729051)
                  ·
                    rfl

theorem cell20_531065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_531065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531065 prefixEnd_531065 := by exact prefixLift 531065
  have htrace : WordTrace (prefixWord ++ tailWord_531065) baseStart_531065 baseEnd_531065 := by
    simpa [prefixWord, tailWord_531065, baseEnd_531065] using wordTrace_append hprefix tailTrace_531065
  have hstable : (prefixWord ++ tailWord_531065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531065).length < 2 ^ (prefixWord ++ tailWord_531065).sum := by decide
  have hdescent : baseEnd_531065 < baseStart_531065 := by decide
  rcases family_descends (prefixWord ++ tailWord_531065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531072 : List Nat := [2, 1, 1, 2, 1, 6, 1, 2, 4]
def baseStart_531072 : Nat := 118140960795 + 531072 * 2 ^ 59
def prefixEnd_531072 : Nat := 4983230072969 + 3 ^ 40 * 531072 * 2
def baseEnd_531072 : Nat := 242395731684134588495689

theorem tailTrace_531072 : CollatzResearch.WordTrace tailWord_531072 prefixEnd_531072 242395731684134588495689 := by
  unfold tailWord_531072
  simp only [CollatzResearch.WordTrace]
  refine ⟨9684893566012159360861735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12913191421349545814482313 9684893566012159360861735)
  ·
    refine ⟨14527340349018239041292603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9684893566012159360861735 14527340349018239041292603)
    ·
      refine ⟨21791010523527358561938905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14527340349018239041292603 21791010523527358561938905)
      ·
        refine ⟨16343257892645518921454179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21791010523527358561938905 16343257892645518921454179)
        ·
          refine ⟨24514886838968278382181269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16343257892645518921454179 24514886838968278382181269)
          ·
            refine ⟨1149135320576638049164747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24514886838968278382181269 1149135320576638049164747)
            ·
              refine ⟨1723702980864957073747121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1149135320576638049164747 1723702980864957073747121)
              ·
                refine ⟨1292777235648717805310341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1723702980864957073747121 1292777235648717805310341)
                ·
                  refine ⟨242395731684134588495689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1292777235648717805310341 242395731684134588495689)
                  ·
                    rfl

theorem cell20_531072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_531072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531072 prefixEnd_531072 := by exact prefixLift 531072
  have htrace : WordTrace (prefixWord ++ tailWord_531072) baseStart_531072 baseEnd_531072 := by
    simpa [prefixWord, tailWord_531072, baseEnd_531072] using wordTrace_append hprefix tailTrace_531072
  have hstable : (prefixWord ++ tailWord_531072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531072).length < 2 ^ (prefixWord ++ tailWord_531072).sum := by decide
  have hdescent : baseEnd_531072 < baseStart_531072 := by decide
  rcases family_descends (prefixWord ++ tailWord_531072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531144 : List Nat := [2, 1, 3, 1, 2, 5, 1, 3, 2]
def baseStart_531144 : Nat := 118140960795 + 531144 * 2 ^ 59
def prefixEnd_531144 : Nat := 4983230072969 + 3 ^ 40 * 531144 * 2
def baseEnd_531144 : Nat := 242428594446022338095395

theorem tailTrace_531144 : CollatzResearch.WordTrace tailWord_531144 prefixEnd_531144 242428594446022338095395 := by
  unfold tailWord_531144
  simp only [CollatzResearch.WordTrace]
  refine ⟨9686206593881737509172243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12914942125175650012229657 9686206593881737509172243)
  ·
    refine ⟨14529309890822606263758365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9686206593881737509172243 14529309890822606263758365)
    ·
      refine ⟨5448491209058477348909387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14529309890822606263758365 5448491209058477348909387)
      ·
        refine ⟨8172736813587716023364081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5448491209058477348909387 8172736813587716023364081)
        ·
          refine ⟨6129552610190787017523061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8172736813587716023364081 6129552610190787017523061)
          ·
            refine ⟨574645557205386282892787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6129552610190787017523061 574645557205386282892787)
            ·
              refine ⟨861968335808079424339181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574645557205386282892787 861968335808079424339181)
              ·
                refine ⟨323238125928029784127193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 861968335808079424339181 323238125928029784127193)
                ·
                  refine ⟨242428594446022338095395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323238125928029784127193 242428594446022338095395)
                  ·
                    rfl

theorem cell20_531144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 2].length) (baseStart_531144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531144 prefixEnd_531144 := by exact prefixLift 531144
  have htrace : WordTrace (prefixWord ++ tailWord_531144) baseStart_531144 baseEnd_531144 := by
    simpa [prefixWord, tailWord_531144, baseEnd_531144] using wordTrace_append hprefix tailTrace_531144
  have hstable : (prefixWord ++ tailWord_531144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531144).length < 2 ^ (prefixWord ++ tailWord_531144).sum := by decide
  have hdescent : baseEnd_531144 < baseStart_531144 := by decide
  rcases family_descends (prefixWord ++ tailWord_531144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531162 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_531162 : Nat := 118140960795 + 531162 * 2 ^ 59
def prefixEnd_531162 : Nat := 4983230072969 + 3 ^ 40 * 531162 * 2
def baseEnd_531162 : Nat := 242436810136494275495321

theorem tailTrace_531162 : CollatzResearch.WordTrace tailWord_531162 prefixEnd_531162 242436810136494275495321 := by
  unfold tailWord_531162
  simp only [CollatzResearch.WordTrace]
  refine ⟨4843267425424566023124935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12915379801132176061666493 4843267425424566023124935)
  ·
    refine ⟨7264901138136849034687403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4843267425424566023124935 7264901138136849034687403)
    ·
      refine ⟨10897351707205273552031105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7264901138136849034687403 10897351707205273552031105)
      ·
        refine ⟨8173013780403955164023329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10897351707205273552031105 8173013780403955164023329)
        ·
          refine ⟨6129760335302966373017497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8173013780403955164023329 6129760335302966373017497)
          ·
            refine ⟨4597320251477224779763123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6129760335302966373017497 4597320251477224779763123)
            ·
              refine ⟨6895980377215837169644685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4597320251477224779763123 6895980377215837169644685)
              ·
                refine ⟨2585992641455938938616757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6895980377215837169644685 2585992641455938938616757)
                ·
                  refine ⟨242436810136494275495321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2585992641455938938616757 242436810136494275495321)
                  ·
                    rfl

theorem cell20_531162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_531162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531162 prefixEnd_531162 := by exact prefixLift 531162
  have htrace : WordTrace (prefixWord ++ tailWord_531162) baseStart_531162 baseEnd_531162 := by
    simpa [prefixWord, tailWord_531162, baseEnd_531162] using wordTrace_append hprefix tailTrace_531162
  have hstable : (prefixWord ++ tailWord_531162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531162).length < 2 ^ (prefixWord ++ tailWord_531162).sum := by decide
  have hdescent : baseEnd_531162 < baseStart_531162 := by decide
  rcases family_descends (prefixWord ++ tailWord_531162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531231 : List Nat := [1, 1, 2, 4, 2, 2, 3, 5]
def baseStart_531231 : Nat := 118140960795 + 531231 * 2 ^ 59
def prefixEnd_531231 : Nat := 4983230072969 + 3 ^ 40 * 531231 * 2
def baseEnd_531231 : Nat := 80822767872212234065013

theorem tailTrace_531231 : CollatzResearch.WordTrace tailWord_531231 prefixEnd_531231 80822767872212234065013 := by
  unfold tailWord_531231
  simp only [CollatzResearch.WordTrace]
  refine ⟨19375586338448288876761547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12917057558965525917841031 19375586338448288876761547)
  ·
    refine ⟨29063379507672433315142321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19375586338448288876761547 29063379507672433315142321)
    ·
      refine ⟨21797534630754324986356741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29063379507672433315142321 21797534630754324986356741)
      ·
        refine ⟨4087037743266435934941889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21797534630754324986356741 4087037743266435934941889)
        ·
          refine ⟨3065278307449826951206417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4087037743266435934941889 3065278307449826951206417)
          ·
            refine ⟨2298958730587370213404813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3065278307449826951206417 2298958730587370213404813)
            ·
              refine ⟨862109523970263830026805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2298958730587370213404813 862109523970263830026805)
              ·
                refine ⟨80822767872212234065013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 862109523970263830026805 80822767872212234065013)
                ·
                  rfl

theorem cell20_531231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 5].length) (baseStart_531231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531231 prefixEnd_531231 := by exact prefixLift 531231
  have htrace : WordTrace (prefixWord ++ tailWord_531231) baseStart_531231 baseEnd_531231 := by
    simpa [prefixWord, tailWord_531231, baseEnd_531231] using wordTrace_append hprefix tailTrace_531231
  have hstable : (prefixWord ++ tailWord_531231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531231).length < 2 ^ (prefixWord ++ tailWord_531231).sum := by decide
  have hdescent : baseEnd_531231 < baseStart_531231 := by decide
  rcases family_descends (prefixWord ++ tailWord_531231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531258 : List Nat := [3, 1, 1, 1, 6, 1, 2, 3, 2]
def baseStart_531258 : Nat := 118140960795 + 531258 * 2 ^ 59
def prefixEnd_531258 : Nat := 4983230072969 + 3 ^ 40 * 531258 * 2
def baseEnd_531258 : Nat := 242480627152344608294929

theorem tailTrace_531258 : CollatzResearch.WordTrace tailWord_531258 prefixEnd_531258 242480627152344608294929 := by
  unfold tailWord_531258
  simp only [CollatzResearch.WordTrace]
  refine ⟨4844142777337618121998607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12917714072900314991996285 4844142777337618121998607)
  ·
    refine ⟨7266214166006427182997911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4844142777337618121998607 7266214166006427182997911)
    ·
      refine ⟨10899321249009640774496867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7266214166006427182997911 10899321249009640774496867)
      ·
        refine ⟨16348981873514461161745301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10899321249009640774496867 16348981873514461161745301)
        ·
          refine ⟨766358525320990366956811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16348981873514461161745301 766358525320990366956811)
          ·
            refine ⟨1149537787981485550435217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766358525320990366956811 1149537787981485550435217)
            ·
              refine ⟨862153340986114162826413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1149537787981485550435217 862153340986114162826413)
              ·
                refine ⟨323307502869792811059905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 862153340986114162826413 323307502869792811059905)
                ·
                  refine ⟨242480627152344608294929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323307502869792811059905 242480627152344608294929)
                  ·
                    rfl

theorem cell20_531258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_531258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531258 prefixEnd_531258 := by exact prefixLift 531258
  have htrace : WordTrace (prefixWord ++ tailWord_531258) baseStart_531258 baseEnd_531258 := by
    simpa [prefixWord, tailWord_531258, baseEnd_531258] using wordTrace_append hprefix tailTrace_531258
  have hstable : (prefixWord ++ tailWord_531258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531258).length < 2 ^ (prefixWord ++ tailWord_531258).sum := by decide
  have hdescent : baseEnd_531258 < baseStart_531258 := by decide
  rcases family_descends (prefixWord ++ tailWord_531258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531268 : List Nat := [2, 3, 4, 2, 1, 2, 1, 2, 3]
def baseStart_531268 : Nat := 118140960795 + 531268 * 2 ^ 59
def prefixEnd_531268 : Nat := 4983230072969 + 3 ^ 40 * 531268 * 2
def baseEnd_531268 : Nat := 242485191424829017961555

theorem tailTrace_531268 : CollatzResearch.WordTrace tailWord_531268 prefixEnd_531268 242485191424829017961555 := by
  unfold tailWord_531268
  simp only [CollatzResearch.WordTrace]
  refine ⟨9688467919657122097929229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12917957226209496130572305 9688467919657122097929229)
  ·
    refine ⟨3633175469871420786723461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9688467919657122097929229 3633175469871420786723461)
    ·
      refine ⟨681220400600891397510649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3633175469871420786723461 681220400600891397510649)
      ·
        refine ⟨510915300450668548132987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681220400600891397510649 510915300450668548132987)
        ·
          refine ⟨766372950676002822199481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510915300450668548132987 766372950676002822199481)
          ·
            refine ⟨574779713007002116649611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766372950676002822199481 574779713007002116649611)
            ·
              refine ⟨862169569510503174974417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574779713007002116649611 862169569510503174974417)
              ·
                refine ⟨646627177132877381230813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 862169569510503174974417 646627177132877381230813)
                ·
                  refine ⟨242485191424829017961555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 646627177132877381230813 242485191424829017961555)
                  ·
                    rfl

theorem cell20_531268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_531268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531268 prefixEnd_531268 := by exact prefixLift 531268
  have htrace : WordTrace (prefixWord ++ tailWord_531268) baseStart_531268 baseEnd_531268 := by
    simpa [prefixWord, tailWord_531268, baseEnd_531268] using wordTrace_append hprefix tailTrace_531268
  have hstable : (prefixWord ++ tailWord_531268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531268).length < 2 ^ (prefixWord ++ tailWord_531268).sum := by decide
  have hdescent : baseEnd_531268 < baseStart_531268 := by decide
  rcases family_descends (prefixWord ++ tailWord_531268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531300 : List Nat := [2, 3, 1, 1, 4, 1, 2, 2, 4]
def baseStart_531300 : Nat := 118140960795 + 531300 * 2 ^ 59
def prefixEnd_531300 : Nat := 4983230072969 + 3 ^ 40 * 531300 * 2
def baseEnd_531300 : Nat := 242499797096779128894757

theorem tailTrace_531300 : CollatzResearch.WordTrace tailWord_531300 prefixEnd_531300 242499797096779128894757 := by
  unfold tailWord_531300
  simp only [CollatzResearch.WordTrace]
  refine ⟨9689051487599156830511677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12918735316798875774015569 9689051487599156830511677)
  ·
    refine ⟨3633394307849683811441879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9689051487599156830511677 3633394307849683811441879)
    ·
      refine ⟨5450091461774525717162819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3633394307849683811441879 5450091461774525717162819)
      ·
        refine ⟨8175137192661788575744229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5450091461774525717162819 8175137192661788575744229)
        ·
          refine ⟨1532838223624085357952043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8175137192661788575744229 1532838223624085357952043)
          ·
            refine ⟨2299257335436128036928065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1532838223624085357952043 2299257335436128036928065)
            ·
              refine ⟨1724443001577096027696049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2299257335436128036928065 1724443001577096027696049)
              ·
                refine ⟨1293332251182822020772037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1724443001577096027696049 1293332251182822020772037)
                ·
                  refine ⟨242499797096779128894757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1293332251182822020772037 242499797096779128894757)
                  ·
                    rfl

theorem cell20_531300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_531300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531300 prefixEnd_531300 := by exact prefixLift 531300
  have htrace : WordTrace (prefixWord ++ tailWord_531300) baseStart_531300 baseEnd_531300 := by
    simpa [prefixWord, tailWord_531300, baseEnd_531300] using wordTrace_append hprefix tailTrace_531300
  have hstable : (prefixWord ++ tailWord_531300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531300).length < 2 ^ (prefixWord ++ tailWord_531300).sum := by decide
  have hdescent : baseEnd_531300 < baseStart_531300 := by decide
  rcases family_descends (prefixWord ++ tailWord_531300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531307 : List Nat := [1, 1, 1, 1, 2, 2, 8, 4]
def baseStart_531307 : Nat := 118140960795 + 531307 * 2 ^ 59
def prefixEnd_531307 : Nat := 4983230072969 + 3 ^ 40 * 531307 * 2
def baseEnd_531307 : Nat := 80834330695839405220465

theorem tailTrace_531307 : CollatzResearch.WordTrace tailWord_531307 prefixEnd_531307 80834330695839405220465 := by
  unfold tailWord_531307
  simp only [CollatzResearch.WordTrace]
  refine ⟨19378358286172953856528175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12918905524115302571018783 19378358286172953856528175)
  ·
    refine ⟨29067537429259430784792263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19378358286172953856528175 29067537429259430784792263)
    ·
      refine ⟨43601306143889146177188395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29067537429259430784792263 43601306143889146177188395)
      ·
        refine ⟨65401959215833719265782593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43601306143889146177188395 65401959215833719265782593)
        ·
          refine ⟨49051469411875289449336945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65401959215833719265782593 49051469411875289449336945)
          ·
            refine ⟨36788602058906467087002709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49051469411875289449336945 36788602058906467087002709)
            ·
              refine ⟨431116430377810161175813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 36788602058906467087002709 431116430377810161175813)
              ·
                refine ⟨80834330695839405220465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 431116430377810161175813 80834330695839405220465)
                ·
                  rfl

theorem cell20_531307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 4].length) (baseStart_531307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531307 prefixEnd_531307 := by exact prefixLift 531307
  have htrace : WordTrace (prefixWord ++ tailWord_531307) baseStart_531307 baseEnd_531307 := by
    simpa [prefixWord, tailWord_531307, baseEnd_531307] using wordTrace_append hprefix tailTrace_531307
  have hstable : (prefixWord ++ tailWord_531307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531307).length < 2 ^ (prefixWord ++ tailWord_531307).sum := by decide
  have hdescent : baseEnd_531307 < baseStart_531307 := by decide
  rcases family_descends (prefixWord ++ tailWord_531307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531314 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_531314 : Nat := 118140960795 + 531314 * 2 ^ 59
def prefixEnd_531314 : Nat := 4983230072969 + 3 ^ 40 * 531314 * 2
def baseEnd_531314 : Nat := 242506187078257302428033

theorem tailTrace_531314 : CollatzResearch.WordTrace tailWord_531314 prefixEnd_531314 242506187078257302428033 := by
  unfold tailWord_531314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4844653399286898513008249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12919075731431729368021997 4844653399286898513008249)
  ·
    refine ⟨3633490049465173884756187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4844653399286898513008249 3633490049465173884756187)
    ·
      refine ⟨5450235074197760827134281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3633490049465173884756187 5450235074197760827134281)
      ·
        refine ⟨4087676305648320620350711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5450235074197760827134281 4087676305648320620350711)
        ·
          refine ⟨6131514458472480930526067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4087676305648320620350711 6131514458472480930526067)
          ·
            refine ⟨9197271687708721395789101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6131514458472480930526067 9197271687708721395789101)
            ·
              refine ⟨3448976882890770523420913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9197271687708721395789101 3448976882890770523420913)
              ·
                refine ⟨2586732662168077892565685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3448976882890770523420913 2586732662168077892565685)
                ·
                  refine ⟨242506187078257302428033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2586732662168077892565685 242506187078257302428033)
                  ·
                    rfl

theorem cell20_531314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_531314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531314 prefixEnd_531314 := by exact prefixLift 531314
  have htrace : WordTrace (prefixWord ++ tailWord_531314) baseStart_531314 baseEnd_531314 := by
    simpa [prefixWord, tailWord_531314, baseEnd_531314] using wordTrace_append hprefix tailTrace_531314
  have hstable : (prefixWord ++ tailWord_531314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531314).length < 2 ^ (prefixWord ++ tailWord_531314).sum := by decide
  have hdescent : baseEnd_531314 < baseStart_531314 := by decide
  rcases family_descends (prefixWord ++ tailWord_531314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531330 : List Nat := [3, 4, 2, 2, 2, 1, 1, 1, 4]
def baseStart_531330 : Nat := 118140960795 + 531330 * 2 ^ 59
def prefixEnd_531330 : Nat := 4983230072969 + 3 ^ 40 * 531330 * 2
def baseEnd_531330 : Nat := 242513489914232357894635

theorem tailTrace_531330 : CollatzResearch.WordTrace tailWord_531330 prefixEnd_531330 242513489914232357894635 := by
  unfold tailWord_531330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4844799291272407196153861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12919464776726419189743629 4844799291272407196153861)
  ·
    refine ⟨908399867113576349278849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4844799291272407196153861 908399867113576349278849)
    ·
      refine ⟨681299900335182261959137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 908399867113576349278849 681299900335182261959137)
      ·
        refine ⟨510974925251386696469353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681299900335182261959137 510974925251386696469353)
        ·
          refine ⟨383231193938540022352015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510974925251386696469353 383231193938540022352015)
          ·
            refine ⟨574846790907810033528023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383231193938540022352015 574846790907810033528023)
            ·
              refine ⟨862270186361715050292035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574846790907810033528023 862270186361715050292035)
              ·
                refine ⟨1293405279542572575438053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862270186361715050292035 1293405279542572575438053)
                ·
                  refine ⟨242513489914232357894635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1293405279542572575438053 242513489914232357894635)
                  ·
                    rfl

theorem cell20_531330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_531330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531330 prefixEnd_531330 := by exact prefixLift 531330
  have htrace : WordTrace (prefixWord ++ tailWord_531330) baseStart_531330 baseEnd_531330 := by
    simpa [prefixWord, tailWord_531330, baseEnd_531330] using wordTrace_append hprefix tailTrace_531330
  have hstable : (prefixWord ++ tailWord_531330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531330).length < 2 ^ (prefixWord ++ tailWord_531330).sum := by decide
  have hdescent : baseEnd_531330 < baseStart_531330 := by decide
  rcases family_descends (prefixWord ++ tailWord_531330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531389 : List Nat := [1, 4, 1, 2, 4, 2, 2, 2, 2]
def baseStart_531389 : Nat := 118140960795 + 531389 * 2 ^ 59
def prefixEnd_531389 : Nat := 4983230072969 + 3 ^ 40 * 531389 * 2
def baseEnd_531389 : Nat := 242540419121890374927727

theorem tailTrace_531389 : CollatzResearch.WordTrace tailWord_531389 prefixEnd_531389 242540419121890374927727 := by
  unfold tailWord_531389
  simp only [CollatzResearch.WordTrace]
  refine ⟨19381349071875881861013221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12920899381250587907342147 19381349071875881861013221)
  ·
    refine ⟨3634002950976727848939979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19381349071875881861013221 3634002950976727848939979)
    ·
      refine ⟨5451004426465091773409969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3634002950976727848939979 5451004426465091773409969)
      ·
        refine ⟨4088253319848818830057477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5451004426465091773409969 4088253319848818830057477)
        ·
          refine ⟨766547497471653530635777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4088253319848818830057477 766547497471653530635777)
          ·
            refine ⟨574910623103740147976833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766547497471653530635777 574910623103740147976833)
            ·
              refine ⟨431182967327805110982625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574910623103740147976833 431182967327805110982625)
              ·
                refine ⟨323387225495853833236969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431182967327805110982625 323387225495853833236969)
                ·
                  refine ⟨242540419121890374927727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323387225495853833236969 242540419121890374927727)
                  ·
                    rfl

theorem cell20_531389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_531389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531389 prefixEnd_531389 := by exact prefixLift 531389
  have htrace : WordTrace (prefixWord ++ tailWord_531389) baseStart_531389 baseEnd_531389 := by
    simpa [prefixWord, tailWord_531389, baseEnd_531389] using wordTrace_append hprefix tailTrace_531389
  have hstable : (prefixWord ++ tailWord_531389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531389).length < 2 ^ (prefixWord ++ tailWord_531389).sum := by decide
  have hdescent : baseEnd_531389 < baseStart_531389 := by decide
  rcases family_descends (prefixWord ++ tailWord_531389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531396 : List Nat := [2, 3, 3, 3, 2, 1, 1, 5]
def baseStart_531396 : Nat := 118140960795 + 531396 * 2 ^ 59
def prefixEnd_531396 : Nat := 4983230072969 + 3 ^ 40 * 531396 * 2
def baseEnd_531396 : Nat := 80847871370876487231455

theorem tailTrace_531396 : CollatzResearch.WordTrace tailWord_531396 prefixEnd_531396 80847871370876487231455 := by
  unfold tailWord_531396
  simp only [CollatzResearch.WordTrace]
  refine ⟨9690802191425261028259021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12921069588567014704345361 9690802191425261028259021)
  ·
    refine ⟨3634050821784472885597133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9690802191425261028259021 3634050821784472885597133)
    ·
      refine ⟨1362769058169177332098925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3634050821784472885597133 1362769058169177332098925)
      ·
        refine ⟨511038396813441499537097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1362769058169177332098925 511038396813441499537097)
        ·
          refine ⟨383278797610081124652823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511038396813441499537097 383278797610081124652823)
          ·
            refine ⟨574918196415121686979235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383278797610081124652823 574918196415121686979235)
            ·
              refine ⟨862377294622682530468853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574918196415121686979235 862377294622682530468853)
              ·
                refine ⟨80847871370876487231455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 862377294622682530468853 80847871370876487231455)
                ·
                  rfl

theorem cell20_531396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 5].length) (baseStart_531396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531396 prefixEnd_531396 := by exact prefixLift 531396
  have htrace : WordTrace (prefixWord ++ tailWord_531396) baseStart_531396 baseEnd_531396 := by
    simpa [prefixWord, tailWord_531396, baseEnd_531396] using wordTrace_append hprefix tailTrace_531396
  have hstable : (prefixWord ++ tailWord_531396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531396).length < 2 ^ (prefixWord ++ tailWord_531396).sum := by decide
  have hdescent : baseEnd_531396 < baseStart_531396 := by decide
  rcases family_descends (prefixWord ++ tailWord_531396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531400 : List Nat := [2, 1, 3, 1, 5, 2, 1, 5]
def baseStart_531400 : Nat := 118140960795 + 531400 * 2 ^ 59
def prefixEnd_531400 : Nat := 4983230072969 + 3 ^ 40 * 531400 * 2
def baseEnd_531400 : Nat := 80848479940541075187005

theorem tailTrace_531400 : CollatzResearch.WordTrace tailWord_531400 prefixEnd_531400 80848479940541075187005 := by
  unfold tailWord_531400
  simp only [CollatzResearch.WordTrace]
  refine ⟨9690875137418015369831827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12921166849890687159775769 9690875137418015369831827)
  ·
    refine ⟨14536312706127023054747741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9690875137418015369831827 14536312706127023054747741)
    ·
      refine ⟨5451117264797633645530403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14536312706127023054747741 5451117264797633645530403)
      ·
        refine ⟨8176675897196450468295605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5451117264797633645530403 8176675897196450468295605)
        ·
          refine ⟨766563365362167231402713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8176675897196450468295605 766563365362167231402713)
          ·
            refine ⟨574922524021625423552035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766563365362167231402713 574922524021625423552035)
            ·
              refine ⟨862383786032438135328053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574922524021625423552035 862383786032438135328053)
              ·
                refine ⟨80848479940541075187005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 862383786032438135328053 80848479940541075187005)
                ·
                  rfl

theorem cell20_531400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_531400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531400 prefixEnd_531400 := by exact prefixLift 531400
  have htrace : WordTrace (prefixWord ++ tailWord_531400) baseStart_531400 baseEnd_531400 := by
    simpa [prefixWord, tailWord_531400, baseEnd_531400] using wordTrace_append hprefix tailTrace_531400
  have hstable : (prefixWord ++ tailWord_531400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531400).length < 2 ^ (prefixWord ++ tailWord_531400).sum := by decide
  have hdescent : baseEnd_531400 < baseStart_531400 := by decide
  rcases family_descends (prefixWord ++ tailWord_531400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531431 : List Nat := [1, 1, 5, 2, 2, 1, 1, 5, 2]
def baseStart_531431 : Nat := 118140960795 + 531431 * 2 ^ 59
def prefixEnd_531431 : Nat := 4983230072969 + 3 ^ 40 * 531431 * 2
def baseEnd_531431 : Nat := 242559589066324895527555

theorem tailTrace_531431 : CollatzResearch.WordTrace tailWord_531431 prefixEnd_531431 242559589066324895527555 := by
  unfold tailWord_531431
  simp only [CollatzResearch.WordTrace]
  refine ⟨19382880937723723034042147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12921920625149148689361431 19382880937723723034042147)
  ·
    refine ⟨29074321406585584551063221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19382880937723723034042147 29074321406585584551063221)
    ·
      refine ⟨2725717631867398551662177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29074321406585584551063221 2725717631867398551662177)
      ·
        refine ⟨2044288223900548913746633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2725717631867398551662177 2044288223900548913746633)
        ·
          refine ⟨1533216167925411685309975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2044288223900548913746633 1533216167925411685309975)
          ·
            refine ⟨2299824251888117527964963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533216167925411685309975 2299824251888117527964963)
            ·
              refine ⟨3449736377832176291947445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2299824251888117527964963 3449736377832176291947445)
              ·
                refine ⟨323412785421766527370073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3449736377832176291947445 323412785421766527370073)
                ·
                  refine ⟨242559589066324895527555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323412785421766527370073 242559589066324895527555)
                  ·
                    rfl

theorem cell20_531431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 2].length) (baseStart_531431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531431 prefixEnd_531431 := by exact prefixLift 531431
  have htrace : WordTrace (prefixWord ++ tailWord_531431) baseStart_531431 baseEnd_531431 := by
    simpa [prefixWord, tailWord_531431, baseEnd_531431] using wordTrace_append hprefix tailTrace_531431
  have hstable : (prefixWord ++ tailWord_531431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531431).length < 2 ^ (prefixWord ++ tailWord_531431).sum := by decide
  have hdescent : baseEnd_531431 < baseStart_531431 := by decide
  rcases family_descends (prefixWord ++ tailWord_531431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531444 : List Nat := [2, 6, 2, 1, 1, 1, 2, 1, 4]
def baseStart_531444 : Nat := 118140960795 + 531444 * 2 ^ 59
def prefixEnd_531444 : Nat := 4983230072969 + 3 ^ 40 * 531444 * 2
def baseEnd_531444 : Nat := 242565522620554628094169

theorem tailTrace_531444 : CollatzResearch.WordTrace tailWord_531444 prefixEnd_531444 242565522620554628094169 := by
  unfold tailWord_531444
  simp only [CollatzResearch.WordTrace]
  refine ⟨9691677543338313127132693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12922236724451084169510257 9691677543338313127132693)
  ·
    refine ⟨454297384843983427834345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9691677543338313127132693 454297384843983427834345)
    ·
      refine ⟨340723038632987570875759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454297384843983427834345 340723038632987570875759)
      ·
        refine ⟨511084557949481356313639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340723038632987570875759 511084557949481356313639)
        ·
          refine ⟨766626836924222034470459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511084557949481356313639 766626836924222034470459)
          ·
            refine ⟨1149940255386333051705689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766626836924222034470459 1149940255386333051705689)
            ·
              refine ⟨862455191539749788779267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1149940255386333051705689 862455191539749788779267)
              ·
                refine ⟨1293682787309624683168901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862455191539749788779267 1293682787309624683168901)
                ·
                  refine ⟨242565522620554628094169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1293682787309624683168901 242565522620554628094169)
                  ·
                    rfl

theorem cell20_531444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_531444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531444 prefixEnd_531444 := by exact prefixLift 531444
  have htrace : WordTrace (prefixWord ++ tailWord_531444) baseStart_531444 baseEnd_531444 := by
    simpa [prefixWord, tailWord_531444, baseEnd_531444] using wordTrace_append hprefix tailTrace_531444
  have hstable : (prefixWord ++ tailWord_531444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531444).length < 2 ^ (prefixWord ++ tailWord_531444).sum := by decide
  have hdescent : baseEnd_531444 < baseStart_531444 := by decide
  rcases family_descends (prefixWord ++ tailWord_531444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531452 : List Nat := [2, 2, 2, 1, 2, 4, 2, 1, 4]
def baseStart_531452 : Nat := 118140960795 + 531452 * 2 ^ 59
def prefixEnd_531452 : Nat := 4983230072969 + 3 ^ 40 * 531452 * 2
def baseEnd_531452 : Nat := 242569174038542155827469

theorem tailTrace_531452 : CollatzResearch.WordTrace tailWord_531452 prefixEnd_531452 242569174038542155827469 := by
  unfold tailWord_531452
  simp only [CollatzResearch.WordTrace]
  refine ⟨9691823435323821810278305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12922431247098429080371073 9691823435323821810278305)
  ·
    refine ⟨7268867576492866357708729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9691823435323821810278305 7268867576492866357708729)
    ·
      refine ⟨5451650682369649768281547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7268867576492866357708729 5451650682369649768281547)
      ·
        refine ⟨8177476023554474652422321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5451650682369649768281547 8177476023554474652422321)
        ·
          refine ⟨6133107017665855989316741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8177476023554474652422321 6133107017665855989316741)
          ·
            refine ⟨1149957565812347997996889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6133107017665855989316741 1149957565812347997996889)
            ·
              refine ⟨862468174359260998497667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1149957565812347997996889 862468174359260998497667)
              ·
                refine ⟨1293702261538891497746501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862468174359260998497667 1293702261538891497746501)
                ·
                  refine ⟨242569174038542155827469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1293702261538891497746501 242569174038542155827469)
                  ·
                    rfl

theorem cell20_531452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_531452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531452 prefixEnd_531452 := by exact prefixLift 531452
  have htrace : WordTrace (prefixWord ++ tailWord_531452) baseStart_531452 baseEnd_531452 := by
    simpa [prefixWord, tailWord_531452, baseEnd_531452] using wordTrace_append hprefix tailTrace_531452
  have hstable : (prefixWord ++ tailWord_531452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531452).length < 2 ^ (prefixWord ++ tailWord_531452).sum := by decide
  have hdescent : baseEnd_531452 < baseStart_531452 := by decide
  rcases family_descends (prefixWord ++ tailWord_531452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531458 : List Nat := [3, 4, 1, 3, 1, 1, 3, 1, 3]
def baseStart_531458 : Nat := 118140960795 + 531458 * 2 ^ 59
def prefixEnd_531458 : Nat := 4983230072969 + 3 ^ 40 * 531458 * 2
def baseEnd_531458 : Nat := 242571912602032801627445

theorem tailTrace_531458 : CollatzResearch.WordTrace tailWord_531458 prefixEnd_531458 242571912602032801627445 := by
  unfold tailWord_531458
  simp only [CollatzResearch.WordTrace]
  refine ⟨4845966427156476661318757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12922577139083937763516685 4845966427156476661318757)
  ·
    refine ⟨908618705091839373997267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4845966427156476661318757 908618705091839373997267)
    ·
      refine ⟨1362928057637759060995901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 908618705091839373997267 1362928057637759060995901)
      ·
        refine ⟨511098021614159647873463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1362928057637759060995901 511098021614159647873463)
        ·
          refine ⟨766647032421239471810195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511098021614159647873463 766647032421239471810195)
          ·
            refine ⟨1149970548631859207715293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766647032421239471810195 1149970548631859207715293)
            ·
              refine ⟨431238955736947202893235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1149970548631859207715293 431238955736947202893235)
              ·
                refine ⟨646858433605420804339853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431238955736947202893235 646858433605420804339853)
                ·
                  refine ⟨242571912602032801627445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 646858433605420804339853 242571912602032801627445)
                  ·
                    rfl

theorem cell20_531458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_531458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531458 prefixEnd_531458 := by exact prefixLift 531458
  have htrace : WordTrace (prefixWord ++ tailWord_531458) baseStart_531458 baseEnd_531458 := by
    simpa [prefixWord, tailWord_531458, baseEnd_531458] using wordTrace_append hprefix tailTrace_531458
  have hstable : (prefixWord ++ tailWord_531458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531458).length < 2 ^ (prefixWord ++ tailWord_531458).sum := by decide
  have hdescent : baseEnd_531458 < baseStart_531458 := by decide
  rcases family_descends (prefixWord ++ tailWord_531458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531504 : List Nat := [2, 1, 1, 1, 2, 4, 2, 4, 3]
def baseStart_531504 : Nat := 118140960795 + 531504 * 2 ^ 59
def prefixEnd_531504 : Nat := 4983230072969 + 3 ^ 40 * 531504 * 2
def baseEnd_531504 : Nat := 242592908255461086093923

theorem tailTrace_531504 : CollatzResearch.WordTrace tailWord_531504 prefixEnd_531504 242592908255461086093923 := by
  unfold tailWord_531504
  simp only [CollatzResearch.WordTrace]
  refine ⟨9692771733229628250724783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12923695644306171000966377 9692771733229628250724783)
  ·
    refine ⟨14539157599844442376087175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9692771733229628250724783 14539157599844442376087175)
    ·
      refine ⟨21808736399766663564130763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14539157599844442376087175 21808736399766663564130763)
      ·
        refine ⟨32713104599649995346196145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21808736399766663564130763 32713104599649995346196145)
        ·
          refine ⟨24534828449737496509647109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32713104599649995346196145 24534828449737496509647109)
          ·
            refine ⟨4600280334325780595558833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24534828449737496509647109 4600280334325780595558833)
            ·
              refine ⟨3450210250744335446669125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4600280334325780595558833 3450210250744335446669125)
              ·
                refine ⟨646914422014562896250461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3450210250744335446669125 646914422014562896250461)
                ·
                  refine ⟨242592908255461086093923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 646914422014562896250461 242592908255461086093923)
                  ·
                    rfl

theorem cell20_531504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_531504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531504 prefixEnd_531504 := by exact prefixLift 531504
  have htrace : WordTrace (prefixWord ++ tailWord_531504) baseStart_531504 baseEnd_531504 := by
    simpa [prefixWord, tailWord_531504, baseEnd_531504] using wordTrace_append hprefix tailTrace_531504
  have hstable : (prefixWord ++ tailWord_531504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531504).length < 2 ^ (prefixWord ++ tailWord_531504).sum := by decide
  have hdescent : baseEnd_531504 < baseStart_531504 := by decide
  rcases family_descends (prefixWord ++ tailWord_531504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531559 : List Nat := [1, 1, 5, 1, 1, 4, 2, 2, 3]
def baseStart_531559 : Nat := 118140960795 + 531559 * 2 ^ 59
def prefixEnd_531559 : Nat := 4983230072969 + 3 ^ 40 * 531559 * 2
def baseEnd_531559 : Nat := 242618011754125339260365

theorem tailTrace_531559 : CollatzResearch.WordTrace tailWord_531559 prefixEnd_531559 242618011754125339260365 := by
  unfold tailWord_531559
  simp only [CollatzResearch.WordTrace]
  refine ⟨19387549481260000894701731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12925032987506667263134487 19387549481260000894701731)
  ·
    refine ⟨29081324221890001342052597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19387549481260000894701731 29081324221890001342052597)
    ·
      refine ⟨2726374145802187625817431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29081324221890001342052597 2726374145802187625817431)
      ·
        refine ⟨4089561218703281438726147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2726374145802187625817431 4089561218703281438726147)
        ·
          refine ⟨6134341828054922158089221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4089561218703281438726147 6134341828054922158089221)
          ·
            refine ⟨1150189092760297904641729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6134341828054922158089221 1150189092760297904641729)
            ·
              refine ⟨862641819570223428481297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1150189092760297904641729 862641819570223428481297)
              ·
                refine ⟨646981364677667571360973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 862641819570223428481297 646981364677667571360973)
                ·
                  refine ⟨242618011754125339260365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 646981364677667571360973 242618011754125339260365)
                  ·
                    rfl

theorem cell20_531559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 3].length) (baseStart_531559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531559 prefixEnd_531559 := by exact prefixLift 531559
  have htrace : WordTrace (prefixWord ++ tailWord_531559) baseStart_531559 baseEnd_531559 := by
    simpa [prefixWord, tailWord_531559, baseEnd_531559] using wordTrace_append hprefix tailTrace_531559
  have hstable : (prefixWord ++ tailWord_531559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531559).length < 2 ^ (prefixWord ++ tailWord_531559).sum := by decide
  have hdescent : baseEnd_531559 < baseStart_531559 := by decide
  rcases family_descends (prefixWord ++ tailWord_531559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531562 : List Nat := [3, 1, 3, 2, 2, 1, 4, 2, 2]
def baseStart_531562 : Nat := 118140960795 + 531562 * 2 ^ 59
def prefixEnd_531562 : Nat := 4983230072969 + 3 ^ 40 * 531562 * 2
def baseEnd_531562 : Nat := 242619381035870662160353

theorem tailTrace_531562 : CollatzResearch.WordTrace tailWord_531562 prefixEnd_531562 242619381035870662160353 := by
  unfold tailWord_531562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4846914725062283101765235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12925105933499421604707293 4846914725062283101765235)
  ·
    refine ⟨7270372087593424652647853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4846914725062283101765235 7270372087593424652647853)
    ·
      refine ⟨2726389532847534244742945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7270372087593424652647853 2726389532847534244742945)
      ·
        refine ⟨2044792149635650683557209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2726389532847534244742945 2044792149635650683557209)
        ·
          refine ⟨1533594112226738012667907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2044792149635650683557209 1533594112226738012667907)
          ·
            refine ⟨2300391168340107019001861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533594112226738012667907 2300391168340107019001861)
            ·
              refine ⟨431323344063770066062849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2300391168340107019001861 431323344063770066062849)
              ·
                refine ⟨323492508047827549547137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431323344063770066062849 323492508047827549547137)
                ·
                  refine ⟨242619381035870662160353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323492508047827549547137 242619381035870662160353)
                  ·
                    rfl

theorem cell20_531562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_531562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531562 prefixEnd_531562 := by exact prefixLift 531562
  have htrace : WordTrace (prefixWord ++ tailWord_531562) baseStart_531562 baseEnd_531562 := by
    simpa [prefixWord, tailWord_531562, baseEnd_531562] using wordTrace_append hprefix tailTrace_531562
  have hstable : (prefixWord ++ tailWord_531562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531562).length < 2 ^ (prefixWord ++ tailWord_531562).sum := by decide
  have hdescent : baseEnd_531562 < baseStart_531562 := by decide
  rcases family_descends (prefixWord ++ tailWord_531562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531580 : List Nat := [2, 2, 2, 1, 1, 3, 1, 5, 3]
def baseStart_531580 : Nat := 118140960795 + 531580 * 2 ^ 59
def prefixEnd_531580 : Nat := 4983230072969 + 3 ^ 40 * 531580 * 2
def baseEnd_531580 : Nat := 242627596726342599560279

theorem tailTrace_531580 : CollatzResearch.WordTrace tailWord_531580 prefixEnd_531580 242627596726342599560279 := by
  unfold tailWord_531580
  simp only [CollatzResearch.WordTrace]
  refine ⟨9694157707091960740608097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12925543609455947654144129 9694157707091960740608097)
  ·
    refine ⟨7270618280318970555456073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9694157707091960740608097 7270618280318970555456073)
    ·
      refine ⟨5452963710239227916592055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7270618280318970555456073 5452963710239227916592055)
      ·
        refine ⟨8179445565358841874888083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5452963710239227916592055 8179445565358841874888083)
        ·
          refine ⟨12269168348038262812332125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8179445565358841874888083 12269168348038262812332125)
          ·
            refine ⟨4600938130514348554624547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12269168348038262812332125 4600938130514348554624547)
            ·
              refine ⟨6901407195771522831936821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4600938130514348554624547 6901407195771522831936821)
              ·
                refine ⟨647006924603580265494077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6901407195771522831936821 647006924603580265494077)
                ·
                  refine ⟨242627596726342599560279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647006924603580265494077 242627596726342599560279)
                  ·
                    rfl

theorem cell20_531580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_531580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531580 prefixEnd_531580 := by exact prefixLift 531580
  have htrace : WordTrace (prefixWord ++ tailWord_531580) baseStart_531580 baseEnd_531580 := by
    simpa [prefixWord, tailWord_531580, baseEnd_531580] using wordTrace_append hprefix tailTrace_531580
  have hstable : (prefixWord ++ tailWord_531580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531580).length < 2 ^ (prefixWord ++ tailWord_531580).sum := by decide
  have hdescent : baseEnd_531580 < baseStart_531580 := by decide
  rcases family_descends (prefixWord ++ tailWord_531580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531587 : List Nat := [1, 1, 1, 3, 3, 2, 3, 2, 4]
def baseStart_531587 : Nat := 118140960795 + 531587 * 2 ^ 59
def prefixEnd_531587 : Nat := 4983230072969 + 3 ^ 40 * 531587 * 2
def baseEnd_531587 : Nat := 242630791717081686326917

theorem tailTrace_531587 : CollatzResearch.WordTrace tailWord_531587 prefixEnd_531587 242630791717081686326917 := by
  unfold tailWord_531587
  simp only [CollatzResearch.WordTrace]
  refine ⟨19388570725158561676721015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12925713816772374451147343 19388570725158561676721015)
  ·
    refine ⟨29082856087737842515081523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19388570725158561676721015 29082856087737842515081523)
    ·
      refine ⟨43624284131606763772622285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29082856087737842515081523 43624284131606763772622285)
      ·
        refine ⟨16359106549352536414733357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43624284131606763772622285 16359106549352536414733357)
        ·
          refine ⟨6134664956007201155525009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16359106549352536414733357 6134664956007201155525009)
          ·
            refine ⟨4600998717005400866643757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6134664956007201155525009 4600998717005400866643757)
            ·
              refine ⟨1725374518877025324991409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4600998717005400866643757 1725374518877025324991409)
              ·
                refine ⟨1294030889157768993743557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1725374518877025324991409 1294030889157768993743557)
                ·
                  refine ⟨242630791717081686326917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1294030889157768993743557 242630791717081686326917)
                  ·
                    rfl

theorem cell20_531587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_531587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531587 prefixEnd_531587 := by exact prefixLift 531587
  have htrace : WordTrace (prefixWord ++ tailWord_531587) baseStart_531587 baseEnd_531587 := by
    simpa [prefixWord, tailWord_531587, baseEnd_531587] using wordTrace_append hprefix tailTrace_531587
  have hstable : (prefixWord ++ tailWord_531587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531587).length < 2 ^ (prefixWord ++ tailWord_531587).sum := by decide
  have hdescent : baseEnd_531587 < baseStart_531587 := by decide
  rcases family_descends (prefixWord ++ tailWord_531587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531614 : List Nat := [4, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_531614 : Nat := 118140960795 + 531614 * 2 ^ 59
def prefixEnd_531614 : Nat := 4983230072969 + 3 ^ 40 * 531614 * 2
def baseEnd_531614 : Nat := 242643115252789592426807

theorem tailTrace_531614 : CollatzResearch.WordTrace tailWord_531614 prefixEnd_531614 242643115252789592426807 := by
  unfold tailWord_531614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2423694437007593160994237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12926370330707163525302597 2423694437007593160994237)
  ·
    refine ⟨908885413877847435372839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2423694437007593160994237 908885413877847435372839)
    ·
      refine ⟨1363328120816771153059259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 908885413877847435372839 1363328120816771153059259)
      ·
        refine ⟨2044992181225156729588889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1363328120816771153059259 2044992181225156729588889)
        ·
          refine ⟨1533744135918867547191667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2044992181225156729588889 1533744135918867547191667)
          ·
            refine ⟨2300616203878301320787501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533744135918867547191667 2300616203878301320787501)
            ·
              refine ⟨862731076454362995295313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2300616203878301320787501 862731076454362995295313)
              ·
                refine ⟨647048307340772246471485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 862731076454362995295313 647048307340772246471485)
                ·
                  refine ⟨242643115252789592426807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647048307340772246471485 242643115252789592426807)
                  ·
                    rfl

theorem cell20_531614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_531614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531614 prefixEnd_531614 := by exact prefixLift 531614
  have htrace : WordTrace (prefixWord ++ tailWord_531614) baseStart_531614 baseEnd_531614 := by
    simpa [prefixWord, tailWord_531614, baseEnd_531614] using wordTrace_append hprefix tailTrace_531614
  have hstable : (prefixWord ++ tailWord_531614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531614).length < 2 ^ (prefixWord ++ tailWord_531614).sum := by decide
  have hdescent : baseEnd_531614 < baseStart_531614 := by decide
  rcases family_descends (prefixWord ++ tailWord_531614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531680 : List Nat := [2, 1, 1, 3, 1, 6, 1, 1, 4]
def baseStart_531680 : Nat := 118140960795 + 531680 * 2 ^ 59
def prefixEnd_531680 : Nat := 4983230072969 + 3 ^ 40 * 531680 * 2
def baseEnd_531680 : Nat := 242673239451186696226537

theorem tailTrace_531680 : CollatzResearch.WordTrace tailWord_531680 prefixEnd_531680 242673239451186696226537 := by
  unfold tailWord_531680
  simp only [CollatzResearch.WordTrace]
  refine ⟨9695981356910819279928247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12927975142547759039904329 9695981356910819279928247)
  ·
    refine ⟨14543972035366228919892371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9695981356910819279928247 14543972035366228919892371)
    ·
      refine ⟨21815958053049343379838557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14543972035366228919892371 21815958053049343379838557)
      ·
        refine ⟨8180984269893503767439459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21815958053049343379838557 8180984269893503767439459)
        ·
          refine ⟨12271476404840255651159189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8180984269893503767439459 12271476404840255651159189)
          ·
            refine ⟨575225456476886983648087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12271476404840255651159189 575225456476886983648087)
            ·
              refine ⟨862838184715330475472131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575225456476886983648087 862838184715330475472131)
              ·
                refine ⟨1294257277072995713208197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862838184715330475472131 1294257277072995713208197)
                ·
                  refine ⟨242673239451186696226537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1294257277072995713208197 242673239451186696226537)
                  ·
                    rfl

theorem cell20_531680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 4].length) (baseStart_531680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531680 prefixEnd_531680 := by exact prefixLift 531680
  have htrace : WordTrace (prefixWord ++ tailWord_531680) baseStart_531680 baseEnd_531680 := by
    simpa [prefixWord, tailWord_531680, baseEnd_531680] using wordTrace_append hprefix tailTrace_531680
  have hstable : (prefixWord ++ tailWord_531680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531680).length < 2 ^ (prefixWord ++ tailWord_531680).sum := by decide
  have hdescent : baseEnd_531680 < baseStart_531680 := by decide
  rcases family_descends (prefixWord ++ tailWord_531680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531690 : List Nat := [3, 1, 3, 1, 1, 5, 2, 1, 3]
def baseStart_531690 : Nat := 118140960795 + 531690 * 2 ^ 59
def prefixEnd_531690 : Nat := 4983230072969 + 3 ^ 40 * 531690 * 2
def baseEnd_531690 : Nat := 242677803723671105893163

theorem tailTrace_531690 : CollatzResearch.WordTrace tailWord_531690 prefixEnd_531690 242677803723671105893163 := by
  unfold tailWord_531690
  simp only [CollatzResearch.WordTrace]
  refine ⟨4848081860946352566930131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12928218295856940178480349 4848081860946352566930131)
  ·
    refine ⟨7272122791419528850395197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4848081860946352566930131 7272122791419528850395197)
    ·
      refine ⟨2727046046782323318898199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7272122791419528850395197 2727046046782323318898199)
      ·
        refine ⟨4090569070173484978347299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2727046046782323318898199 4090569070173484978347299)
        ·
          refine ⟨6135853605260227467520949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4090569070173484978347299 6135853605260227467520949)
          ·
            refine ⟨575236275493146325080089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6135853605260227467520949 575236275493146325080089)
            ·
              refine ⟨431427206619859743810067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575236275493146325080089 431427206619859743810067)
              ·
                refine ⟨647140809929789615715101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431427206619859743810067 647140809929789615715101)
                ·
                  refine ⟨242677803723671105893163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647140809929789615715101 242677803723671105893163)
                  ·
                    rfl

theorem cell20_531690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_531690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531690 prefixEnd_531690 := by exact prefixLift 531690
  have htrace : WordTrace (prefixWord ++ tailWord_531690) baseStart_531690 baseEnd_531690 := by
    simpa [prefixWord, tailWord_531690, baseEnd_531690] using wordTrace_append hprefix tailTrace_531690
  have hstable : (prefixWord ++ tailWord_531690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531690).length < 2 ^ (prefixWord ++ tailWord_531690).sum := by decide
  have hdescent : baseEnd_531690 < baseStart_531690 := by decide
  rcases family_descends (prefixWord ++ tailWord_531690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531763 : List Nat := [1, 1, 1, 2, 5, 3, 3, 4]
def baseStart_531763 : Nat := 118140960795 + 531763 * 2 ^ 59
def prefixEnd_531763 : Nat := 4983230072969 + 3 ^ 40 * 531763 * 2
def baseEnd_531763 : Nat := 80903707637602432153177

theorem tailTrace_531763 : CollatzResearch.WordTrace tailWord_531763 prefixEnd_531763 80903707637602432153177 := by
  unfold tailWord_531763
  simp only [CollatzResearch.WordTrace]
  refine ⟨19394989972520943735127943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12929993315013962490085295 19394989972520943735127943)
  ·
    refine ⟨29092484958781415602691915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19394989972520943735127943 29092484958781415602691915)
    ·
      refine ⟨43638727438172123404037873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29092484958781415602691915 43638727438172123404037873)
      ·
        refine ⟨32729045578629092553028405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43638727438172123404037873 32729045578629092553028405)
        ·
          refine ⟨3068348022996477426846413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32729045578629092553028405 3068348022996477426846413)
          ·
            refine ⟨1150630508623679035067405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3068348022996477426846413 1150630508623679035067405)
            ·
              refine ⟨431486440733879638150277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1150630508623679035067405 431486440733879638150277)
              ·
                refine ⟨80903707637602432153177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 431486440733879638150277 80903707637602432153177)
                ·
                  rfl

theorem cell20_531763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 4].length) (baseStart_531763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531763 prefixEnd_531763 := by exact prefixLift 531763
  have htrace : WordTrace (prefixWord ++ tailWord_531763) baseStart_531763 baseEnd_531763 := by
    simpa [prefixWord, tailWord_531763, baseEnd_531763] using wordTrace_append hprefix tailTrace_531763
  have hstable : (prefixWord ++ tailWord_531763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531763).length < 2 ^ (prefixWord ++ tailWord_531763).sum := by decide
  have hdescent : baseEnd_531763 < baseStart_531763 := by decide
  rcases family_descends (prefixWord ++ tailWord_531763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531849 : List Nat := [1, 2, 1, 1, 8, 1, 1, 1, 4]
def baseStart_531849 : Nat := 118140960795 + 531849 * 2 ^ 59
def prefixEnd_531849 : Nat := 4983230072969 + 3 ^ 40 * 531849 * 2
def baseEnd_531849 : Nat := 242750375656173219592513

theorem tailTrace_531849 : CollatzResearch.WordTrace tailWord_531849 prefixEnd_531849 242750375656173219592513 := by
  unfold tailWord_531849
  simp only [CollatzResearch.WordTrace]
  refine ⟨19398126650209380422758601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12932084433472920281839067 19398126650209380422758601)
  ·
    refine ⟨14548594987657035317068951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19398126650209380422758601 14548594987657035317068951)
    ·
      refine ⟨21822892481485552975603427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14548594987657035317068951 21822892481485552975603427)
      ·
        refine ⟨32734338722228329463405141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21822892481485552975603427 32734338722228329463405141)
        ·
          refine ⟨383605531901113235899279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 32734338722228329463405141 383605531901113235899279)
          ·
            refine ⟨575408297851669853848919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383605531901113235899279 575408297851669853848919)
            ·
              refine ⟨863112446777504780773379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575408297851669853848919 863112446777504780773379)
              ·
                refine ⟨1294668670166257171160069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863112446777504780773379 1294668670166257171160069)
                ·
                  refine ⟨242750375656173219592513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1294668670166257171160069 242750375656173219592513)
                  ·
                    rfl

theorem cell20_531849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 4].length) (baseStart_531849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531849 prefixEnd_531849 := by exact prefixLift 531849
  have htrace : WordTrace (prefixWord ++ tailWord_531849) baseStart_531849 baseEnd_531849 := by
    simpa [prefixWord, tailWord_531849, baseEnd_531849] using wordTrace_append hprefix tailTrace_531849
  have hstable : (prefixWord ++ tailWord_531849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531849).length < 2 ^ (prefixWord ++ tailWord_531849).sum := by decide
  have hdescent : baseEnd_531849 < baseStart_531849 := by decide
  rcases family_descends (prefixWord ++ tailWord_531849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531929 : List Nat := [1, 2, 1, 2, 4, 3, 1, 2, 4]
def baseStart_531929 : Nat := 118140960795 + 531929 * 2 ^ 59
def prefixEnd_531929 : Nat := 4983230072969 + 3 ^ 40 * 531929 * 2
def baseEnd_531929 : Nat := 242786889836048496925519

theorem tailTrace_531929 : CollatzResearch.WordTrace tailWord_531929 prefixEnd_531929 242786889836048496925519 := by
  unfold tailWord_531929
  simp only [CollatzResearch.WordTrace]
  refine ⟨19401044489919554085670841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12934029659946369390447227 19401044489919554085670841)
  ·
    refine ⟨14550783367439665564253131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19401044489919554085670841 14550783367439665564253131)
    ·
      refine ⟨21826175051159498346379697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14550783367439665564253131 21826175051159498346379697)
      ·
        refine ⟨16369631288369623759784773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21826175051159498346379697 16369631288369623759784773)
        ·
          refine ⟨3069305866569304454959645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16369631288369623759784773 3069305866569304454959645)
          ·
            refine ⟨1150989699963489170609867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3069305866569304454959645 1150989699963489170609867)
            ·
              refine ⟨1726484549945233755914801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1150989699963489170609867 1726484549945233755914801)
              ·
                refine ⟨1294863412458925316936101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1726484549945233755914801 1294863412458925316936101)
                ·
                  refine ⟨242786889836048496925519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1294863412458925316936101 242786889836048496925519)
                  ·
                    rfl

theorem cell20_531929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_531929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531929 prefixEnd_531929 := by exact prefixLift 531929
  have htrace : WordTrace (prefixWord ++ tailWord_531929) baseStart_531929 baseEnd_531929 := by
    simpa [prefixWord, tailWord_531929, baseEnd_531929] using wordTrace_append hprefix tailTrace_531929
  have hstable : (prefixWord ++ tailWord_531929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531929).length < 2 ^ (prefixWord ++ tailWord_531929).sum := by decide
  have hdescent : baseEnd_531929 < baseStart_531929 := by decide
  rcases family_descends (prefixWord ++ tailWord_531929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531960 : List Nat := [2, 1, 2, 1, 1, 5, 3, 2, 3]
def baseStart_531960 : Nat := 118140960795 + 531960 * 2 ^ 59
def prefixEnd_531960 : Nat := 4983230072969 + 3 ^ 40 * 531960 * 2
def baseEnd_531960 : Nat := 242801039080750166892059

theorem tailTrace_531960 : CollatzResearch.WordTrace tailWord_531960 prefixEnd_531960 242801039080750166892059 := by
  unfold tailWord_531960
  simp only [CollatzResearch.WordTrace]
  refine ⟨9701087576403623190024667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12934783435204830920032889 9701087576403623190024667)
  ·
    refine ⟨14551631364605434785037001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9701087576403623190024667 14551631364605434785037001)
    ·
      refine ⟨10913723523454076088777751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14551631364605434785037001 10913723523454076088777751)
      ·
        refine ⟨16370585285181114133166627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10913723523454076088777751 16370585285181114133166627)
        ·
          refine ⟨24555877927771671199749941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16370585285181114133166627 24555877927771671199749941)
          ·
            refine ⟨2302113555728594174976557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24555877927771671199749941 2302113555728594174976557)
            ·
              refine ⟨863292583398222815616209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2302113555728594174976557 863292583398222815616209)
              ·
                refine ⟨647469437548667111712157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 863292583398222815616209 647469437548667111712157)
                ·
                  refine ⟨242801039080750166892059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647469437548667111712157 242801039080750166892059)
                  ·
                    rfl

theorem cell20_531960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_531960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_531960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_531960 prefixEnd_531960 := by exact prefixLift 531960
  have htrace : WordTrace (prefixWord ++ tailWord_531960) baseStart_531960 baseEnd_531960 := by
    simpa [prefixWord, tailWord_531960, baseEnd_531960] using wordTrace_append hprefix tailTrace_531960
  have hstable : (prefixWord ++ tailWord_531960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531960).length < 2 ^ (prefixWord ++ tailWord_531960).sum := by decide
  have hdescent : baseEnd_531960 < baseStart_531960 := by decide
  rcases family_descends (prefixWord ++ tailWord_531960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532001 : List Nat := [1, 2, 3, 2, 2, 4, 1, 3, 2]
def baseStart_532001 : Nat := 118140960795 + 532001 * 2 ^ 59
def prefixEnd_532001 : Nat := 4983230072969 + 3 ^ 40 * 532001 * 2
def baseEnd_532001 : Nat := 242819752597936246525225

theorem tailTrace_532001 : CollatzResearch.WordTrace tailWord_532001 prefixEnd_532001 242819752597936246525225 := by
  unfold tailWord_532001
  simp only [CollatzResearch.WordTrace]
  refine ⟨19403670545658710382291857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12935780363772473588194571 19403670545658710382291857)
  ·
    refine ⟨14552752909244032786718893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19403670545658710382291857 14552752909244032786718893)
    ·
      refine ⟨5457282340966512295019585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14552752909244032786718893 5457282340966512295019585)
      ·
        refine ⟨4092961755724884221264689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5457282340966512295019585 4092961755724884221264689)
        ·
          refine ⟨3069721316793663165948517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4092961755724884221264689 3069721316793663165948517)
          ·
            refine ⟨575572746898811843615347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3069721316793663165948517 575572746898811843615347)
            ·
              refine ⟨863359120348217765423021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575572746898811843615347 863359120348217765423021)
              ·
                refine ⟨323759670130581662033633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 863359120348217765423021 323759670130581662033633)
                ·
                  refine ⟨242819752597936246525225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323759670130581662033633 242819752597936246525225)
                  ·
                    rfl

theorem cell20_532001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 2].length) (baseStart_532001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532001 prefixEnd_532001 := by exact prefixLift 532001
  have htrace : WordTrace (prefixWord ++ tailWord_532001) baseStart_532001 baseEnd_532001 := by
    simpa [prefixWord, tailWord_532001, baseEnd_532001] using wordTrace_append hprefix tailTrace_532001
  have hstable : (prefixWord ++ tailWord_532001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532001).length < 2 ^ (prefixWord ++ tailWord_532001).sum := by decide
  have hdescent : baseEnd_532001 < baseStart_532001 := by decide
  rcases family_descends (prefixWord ++ tailWord_532001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532008 : List Nat := [2, 1, 5, 2, 3, 1, 6]
def baseStart_532008 : Nat := 118140960795 + 532008 * 2 ^ 59
def prefixEnd_532008 : Nat := 4983230072969 + 3 ^ 40 * 532008 * 2
def baseEnd_532008 : Nat := 26980327509852814810207

theorem tailTrace_532008 : CollatzResearch.WordTrace tailWord_532008 prefixEnd_532008 26980327509852814810207 := by
  unfold tailWord_532008
  simp only [CollatzResearch.WordTrace]
  refine ⟨9701962928316675288898339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12935950571088900385197785 9701962928316675288898339)
  ·
    refine ⟨14552944392475012933347509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9701962928316675288898339 14552944392475012933347509)
    ·
      refine ⟨1364338536794532462501329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14552944392475012933347509 1364338536794532462501329)
      ·
        refine ⟨1023253902595899346875997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1364338536794532462501329 1023253902595899346875997)
        ·
          refine ⟨383720213473462255078499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1023253902595899346875997 383720213473462255078499)
          ·
            refine ⟨575580320210193382617749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383720213473462255078499 575580320210193382617749)
            ·
              refine ⟨26980327509852814810207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 575580320210193382617749 26980327509852814810207)
              ·
                rfl

theorem cell20_532008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 6].length) (baseStart_532008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532008 prefixEnd_532008 := by exact prefixLift 532008
  have htrace : WordTrace (prefixWord ++ tailWord_532008) baseStart_532008 baseEnd_532008 := by
    simpa [prefixWord, tailWord_532008, baseEnd_532008] using wordTrace_append hprefix tailTrace_532008
  have hstable : (prefixWord ++ tailWord_532008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532008).length < 2 ^ (prefixWord ++ tailWord_532008).sum := by decide
  have hdescent : baseEnd_532008 < baseStart_532008 := by decide
  rcases family_descends (prefixWord ++ tailWord_532008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532019 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 5]
def baseStart_532019 : Nat := 118140960795 + 532019 * 2 ^ 59
def prefixEnd_532019 : Nat := 4983230072969 + 3 ^ 40 * 532019 * 2
def baseEnd_532019 : Nat := 242827968288408183925151

theorem tailTrace_532019 : CollatzResearch.WordTrace tailWord_532019 prefixEnd_532019 242827968288408183925151 := by
  unfold tailWord_532019
  simp only [CollatzResearch.WordTrace]
  refine ⟨19404327059593499456447111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12936218039728999637631407 19404327059593499456447111)
  ·
    refine ⟨29106490589390249184670667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19404327059593499456447111 29106490589390249184670667)
    ·
      refine ⟨43659735884085373777006001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29106490589390249184670667 43659735884085373777006001)
      ·
        refine ⟨32744801913064030332754501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43659735884085373777006001 32744801913064030332754501)
        ·
          refine ⟨6139650358699505687391469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32744801913064030332754501 6139650358699505687391469)
          ·
            refine ⟨2302368884512314632771801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6139650358699505687391469 2302368884512314632771801)
            ·
              refine ⟨1726776663384235974578851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2302368884512314632771801 1726776663384235974578851)
              ·
                refine ⟨2590164995076353961868277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1726776663384235974578851 2590164995076353961868277)
                ·
                  refine ⟨242827968288408183925151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2590164995076353961868277 242827968288408183925151)
                  ·
                    rfl

theorem cell20_532019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_532019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532019 prefixEnd_532019 := by exact prefixLift 532019
  have htrace : WordTrace (prefixWord ++ tailWord_532019) baseStart_532019 baseEnd_532019 := by
    simpa [prefixWord, tailWord_532019, baseEnd_532019] using wordTrace_append hprefix tailTrace_532019
  have hstable : (prefixWord ++ tailWord_532019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532019).length < 2 ^ (prefixWord ++ tailWord_532019).sum := by decide
  have hdescent : baseEnd_532019 < baseStart_532019 := by decide
  rcases family_descends (prefixWord ++ tailWord_532019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532029 : List Nat := [1, 4, 1, 3, 3, 1, 2, 5]
def baseStart_532029 : Nat := 118140960795 + 532029 * 2 ^ 59
def prefixEnd_532029 : Nat := 4983230072969 + 3 ^ 40 * 532029 * 2
def baseEnd_532029 : Nat := 80944177520297531197259

theorem tailTrace_532029 : CollatzResearch.WordTrace tailWord_532029 prefixEnd_532029 80944177520297531197259 := by
  unfold tailWord_532029
  simp only [CollatzResearch.WordTrace]
  refine ⟨19404691789557271164311141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12936461193038180776207427 19404691789557271164311141)
  ·
    refine ⟨3638379710541988343308339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19404691789557271164311141 3638379710541988343308339)
    ·
      refine ⟨5457569565812982514962509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3638379710541988343308339 5457569565812982514962509)
      ·
        refine ⟨2046588587179868443110941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5457569565812982514962509 2046588587179868443110941)
        ·
          refine ⟨767470720192450666166603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2046588587179868443110941 767470720192450666166603)
          ·
            refine ⟨1151206080288675999249905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767470720192450666166603 1151206080288675999249905)
            ·
              refine ⟨863404560216506999437429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1151206080288675999249905 863404560216506999437429)
              ·
                refine ⟨80944177520297531197259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 863404560216506999437429 80944177520297531197259)
                ·
                  rfl

theorem cell20_532029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 5].length) (baseStart_532029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532029 prefixEnd_532029 := by exact prefixLift 532029
  have htrace : WordTrace (prefixWord ++ tailWord_532029) baseStart_532029 baseEnd_532029 := by
    simpa [prefixWord, tailWord_532029, baseEnd_532029] using wordTrace_append hprefix tailTrace_532029
  have hstable : (prefixWord ++ tailWord_532029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532029).length < 2 ^ (prefixWord ++ tailWord_532029).sum := by decide
  have hdescent : baseEnd_532029 < baseStart_532029 := by decide
  rcases family_descends (prefixWord ++ tailWord_532029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532050 : List Nat := [3, 2, 2, 1, 2, 2, 2, 6]
def baseStart_532050 : Nat := 118140960795 + 532050 * 2 ^ 59
def prefixEnd_532050 : Nat := 4983230072969 + 3 ^ 40 * 532050 * 2
def baseEnd_532050 : Nat := 80947372511036617963897

theorem tailTrace_532050 : CollatzResearch.WordTrace tailWord_532050 prefixEnd_532050 80947372511036617963897 := by
  unfold tailWord_532050
  simp only [CollatzResearch.WordTrace]
  refine ⟨4851364430620297937706401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12936971814987461167217069 4851364430620297937706401)
  ·
    refine ⟨3638523322965223453279801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4851364430620297937706401 3638523322965223453279801)
    ·
      refine ⟨2728892492223917589959851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3638523322965223453279801 2728892492223917589959851)
      ·
        refine ⟨4093338738335876384939777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2728892492223917589959851 4093338738335876384939777)
        ·
          refine ⟨3070004053751907288704833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4093338738335876384939777 3070004053751907288704833)
          ·
            refine ⟨2302503040313930466528625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3070004053751907288704833 2302503040313930466528625)
            ·
              refine ⟨1726877280235447849896469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2302503040313930466528625 1726877280235447849896469)
              ·
                refine ⟨80947372511036617963897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1726877280235447849896469 80947372511036617963897)
                ·
                  rfl

theorem cell20_532050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_532050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532050 prefixEnd_532050 := by exact prefixLift 532050
  have htrace : WordTrace (prefixWord ++ tailWord_532050) baseStart_532050 baseEnd_532050 := by
    simpa [prefixWord, tailWord_532050, baseEnd_532050] using wordTrace_append hprefix tailTrace_532050
  have hstable : (prefixWord ++ tailWord_532050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532050).length < 2 ^ (prefixWord ++ tailWord_532050).sum := by decide
  have hdescent : baseEnd_532050 < baseStart_532050 := by decide
  rcases family_descends (prefixWord ++ tailWord_532050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532074 : List Nat := [3, 1, 3, 2, 1, 2, 1, 4, 3]
def baseStart_532074 : Nat := 118140960795 + 532074 * 2 ^ 59
def prefixEnd_532074 : Nat := 4983230072969 + 3 ^ 40 * 532074 * 2
def baseEnd_532074 : Nat := 242853071787072437091593

theorem tailTrace_532074 : CollatzResearch.WordTrace tailWord_532074 prefixEnd_532074 242853071787072437091593 := by
  unfold tailWord_532074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4851583268598560962424819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12937555382929495899799517 4851583268598560962424819)
  ·
    refine ⟨7277374902897841443637229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4851583268598560962424819 7277374902897841443637229)
    ·
      refine ⟨2729015588586690541363961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7277374902897841443637229 2729015588586690541363961)
      ·
        refine ⟨2046761691440017906022971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2729015588586690541363961 2046761691440017906022971)
        ·
          refine ⟨3070142537160026859034457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2046761691440017906022971 3070142537160026859034457)
          ·
            refine ⟨2302606902870020144275843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3070142537160026859034457 2302606902870020144275843)
            ·
              refine ⟨3453910354305030216413765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2302606902870020144275843 3453910354305030216413765)
              ·
                refine ⟨647608191432193165577581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3453910354305030216413765 647608191432193165577581)
                ·
                  refine ⟨242853071787072437091593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647608191432193165577581 242853071787072437091593)
                  ·
                    rfl

theorem cell20_532074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_532074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532074 prefixEnd_532074 := by exact prefixLift 532074
  have htrace : WordTrace (prefixWord ++ tailWord_532074) baseStart_532074 baseEnd_532074 := by
    simpa [prefixWord, tailWord_532074, baseEnd_532074] using wordTrace_append hprefix tailTrace_532074
  have hstable : (prefixWord ++ tailWord_532074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532074).length < 2 ^ (prefixWord ++ tailWord_532074).sum := by decide
  have hdescent : baseEnd_532074 < baseStart_532074 := by decide
  rcases family_descends (prefixWord ++ tailWord_532074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532077 : List Nat := [1, 5, 1, 1, 4, 1, 1, 4, 2]
def baseStart_532077 : Nat := 118140960795 + 532077 * 2 ^ 59
def prefixEnd_532077 : Nat := 4983230072969 + 3 ^ 40 * 532077 * 2
def baseEnd_532077 : Nat := 242854441068817759991581

theorem tailTrace_532077 : CollatzResearch.WordTrace tailWord_532077 prefixEnd_532077 242854441068817759991581 := by
  unfold tailWord_532077
  simp only [CollatzResearch.WordTrace]
  refine ⟨19406442493383375362058485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12937628328922250241372323 19406442493383375362058485)
  ·
    refine ⟨1819353983754691440192983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19406442493383375362058485 1819353983754691440192983)
    ·
      refine ⟨2729030975632037160289475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1819353983754691440192983 2729030975632037160289475)
      ·
        refine ⟨4093546463448055740434213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2729030975632037160289475 4093546463448055740434213)
        ·
          refine ⟨767539961896510451331415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4093546463448055740434213 767539961896510451331415)
          ·
            refine ⟨1151309942844765676997123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767539961896510451331415 1151309942844765676997123)
            ·
              refine ⟨1726964914267148515495685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1151309942844765676997123 1726964914267148515495685)
              ·
                refine ⟨323805921425090346655441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1726964914267148515495685 323805921425090346655441)
                ·
                  refine ⟨242854441068817759991581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323805921425090346655441 242854441068817759991581)
                  ·
                    rfl

theorem cell20_532077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_532077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532077 prefixEnd_532077 := by exact prefixLift 532077
  have htrace : WordTrace (prefixWord ++ tailWord_532077) baseStart_532077 baseEnd_532077 := by
    simpa [prefixWord, tailWord_532077, baseEnd_532077] using wordTrace_append hprefix tailTrace_532077
  have hstable : (prefixWord ++ tailWord_532077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532077).length < 2 ^ (prefixWord ++ tailWord_532077).sum := by decide
  have hdescent : baseEnd_532077 < baseStart_532077 := by decide
  rcases family_descends (prefixWord ++ tailWord_532077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532129 : List Nat := [1, 2, 3, 3, 2, 3, 1, 2, 3]
def baseStart_532129 : Nat := 118140960795 + 532129 * 2 ^ 59
def prefixEnd_532129 : Nat := 4983230072969 + 3 ^ 40 * 532129 * 2
def baseEnd_532129 : Nat := 242878175285736690258035

theorem tailTrace_532129 : CollatzResearch.WordTrace tailWord_532129 prefixEnd_532129 242878175285736690258035 := by
  unfold tailWord_532129
  simp only [CollatzResearch.WordTrace]
  refine ⟨19408339089194988242951441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12938892726129992161967627 19408339089194988242951441)
  ·
    refine ⟨14556254316896241182213581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19408339089194988242951441 14556254316896241182213581)
    ·
      refine ⟨5458595368836090443330093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14556254316896241182213581 5458595368836090443330093)
      ·
        refine ⟨2046973263313533916248785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5458595368836090443330093 2046973263313533916248785)
        ·
          refine ⟨1535229947485150437186589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2046973263313533916248785 1535229947485150437186589)
          ·
            refine ⟨575711230306931413944971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1535229947485150437186589 575711230306931413944971)
            ·
              refine ⟨863566845460397120917457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575711230306931413944971 863566845460397120917457)
              ·
                refine ⟨647675134095297840688093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 863566845460397120917457 647675134095297840688093)
                ·
                  refine ⟨242878175285736690258035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647675134095297840688093 242878175285736690258035)
                  ·
                    rfl

theorem cell20_532129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 3].length) (baseStart_532129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532129 prefixEnd_532129 := by exact prefixLift 532129
  have htrace : WordTrace (prefixWord ++ tailWord_532129) baseStart_532129 baseEnd_532129 := by
    simpa [prefixWord, tailWord_532129, baseEnd_532129] using wordTrace_append hprefix tailTrace_532129
  have hstable : (prefixWord ++ tailWord_532129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532129).length < 2 ^ (prefixWord ++ tailWord_532129).sum := by decide
  have hdescent : baseEnd_532129 < baseStart_532129 := by decide
  rcases family_descends (prefixWord ++ tailWord_532129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532147 : List Nat := [1, 1, 1, 2, 3, 3, 2, 7]
def baseStart_532147 : Nat := 118140960795 + 532147 * 2 ^ 59
def prefixEnd_532147 : Nat := 4983230072969 + 3 ^ 40 * 532147 * 2
def baseEnd_532147 : Nat := 80962130325402875885987

theorem tailTrace_532147 : CollatzResearch.WordTrace tailWord_532147 prefixEnd_532147 80962130325402875885987 := by
  unfold tailWord_532147
  simp only [CollatzResearch.WordTrace]
  refine ⟨19408995603129777317106695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12939330402086518211404463 19408995603129777317106695)
  ·
    refine ⟨29113493404694665975660043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19408995603129777317106695 29113493404694665975660043)
    ·
      refine ⟨43670240107041998963490065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29113493404694665975660043 43670240107041998963490065)
      ·
        refine ⟨32752680080281499222617549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43670240107041998963490065 32752680080281499222617549)
        ·
          refine ⟨12282255030105562208481581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32752680080281499222617549 12282255030105562208481581)
          ·
            refine ⟨4605845636289585828180593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12282255030105562208481581 4605845636289585828180593)
            ·
              refine ⟨3454384227217189371135445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4605845636289585828180593 3454384227217189371135445)
              ·
                refine ⟨80962130325402875885987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3454384227217189371135445 80962130325402875885987)
                ·
                  rfl

theorem cell20_532147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 7].length) (baseStart_532147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532147 prefixEnd_532147 := by exact prefixLift 532147
  have htrace : WordTrace (prefixWord ++ tailWord_532147) baseStart_532147 baseEnd_532147 := by
    simpa [prefixWord, tailWord_532147, baseEnd_532147] using wordTrace_append hprefix tailTrace_532147
  have hstable : (prefixWord ++ tailWord_532147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532147).length < 2 ^ (prefixWord ++ tailWord_532147).sum := by decide
  have hdescent : baseEnd_532147 < baseStart_532147 := by decide
  rcases family_descends (prefixWord ++ tailWord_532147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532164 : List Nat := [2, 3, 3, 1, 1, 1, 3, 6]
def baseStart_532164 : Nat := 118140960795 + 532164 * 2 ^ 59
def prefixEnd_532164 : Nat := 4983230072969 + 3 ^ 40 * 532164 * 2
def baseEnd_532164 : Nat := 80964716746477374697075

theorem tailTrace_532164 : CollatzResearch.WordTrace tailWord_532164 prefixEnd_532164 80964716746477374697075 := by
  unfold tailWord_532164
  simp only [CollatzResearch.WordTrace]
  refine ⟨9704807822034094610237773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12939743762712126146983697 9704807822034094610237773)
  ·
    refine ⟨3639302933262785478839165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9704807822034094610237773 3639302933262785478839165)
    ·
      refine ⟨1364738599973544554564687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3639302933262785478839165 1364738599973544554564687)
      ·
        refine ⟨2047107899960316831847031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1364738599973544554564687 2047107899960316831847031)
        ·
          refine ⟨3070661849940475247770547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2047107899960316831847031 3070661849940475247770547)
          ·
            refine ⟨4605992774910712871655821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3070661849940475247770547 4605992774910712871655821)
            ·
              refine ⟨1727247290591517326870933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4605992774910712871655821 1727247290591517326870933)
              ·
                refine ⟨80964716746477374697075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1727247290591517326870933 80964716746477374697075)
                ·
                  rfl

theorem cell20_532164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_532164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532164 prefixEnd_532164 := by exact prefixLift 532164
  have htrace : WordTrace (prefixWord ++ tailWord_532164) baseStart_532164 baseEnd_532164 := by
    simpa [prefixWord, tailWord_532164, baseEnd_532164] using wordTrace_append hprefix tailTrace_532164
  have hstable : (prefixWord ++ tailWord_532164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532164).length < 2 ^ (prefixWord ++ tailWord_532164).sum := by decide
  have hdescent : baseEnd_532164 < baseStart_532164 := by decide
  rcases family_descends (prefixWord ++ tailWord_532164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532170 : List Nat := [3, 1, 2, 1, 6, 1, 1, 3, 2]
def baseStart_532170 : Nat := 118140960795 + 532170 * 2 ^ 59
def prefixEnd_532170 : Nat := 4983230072969 + 3 ^ 40 * 532170 * 2
def baseEnd_532170 : Nat := 242896888802922769891201

theorem tailTrace_532170 : CollatzResearch.WordTrace tailWord_532170 prefixEnd_532170 242896888802922769891201 := by
  unfold tailWord_532170
  simp only [CollatzResearch.WordTrace]
  refine ⟨4852458620511613061298491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12939889654697634830129309 4852458620511613061298491)
  ·
    refine ⟨7278687930767419591947737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4852458620511613061298491 7278687930767419591947737)
    ·
      refine ⟨5459015948075564693960803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7278687930767419591947737 5459015948075564693960803)
      ·
        refine ⟨8188523922113347040941205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5459015948075564693960803 8188523922113347040941205)
        ·
          refine ⟨383837058849063142544119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8188523922113347040941205 383837058849063142544119)
          ·
            refine ⟨575755588273594713816179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383837058849063142544119 575755588273594713816179)
            ·
              refine ⟨863633382410392070724269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575755588273594713816179 863633382410392070724269)
              ·
                refine ⟨323862518403897026521601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 863633382410392070724269 323862518403897026521601)
                ·
                  refine ⟨242896888802922769891201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323862518403897026521601 242896888802922769891201)
                  ·
                    rfl

theorem cell20_532170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_532170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532170 prefixEnd_532170 := by exact prefixLift 532170
  have htrace : WordTrace (prefixWord ++ tailWord_532170) baseStart_532170 baseEnd_532170 := by
    simpa [prefixWord, tailWord_532170, baseEnd_532170] using wordTrace_append hprefix tailTrace_532170
  have hstable : (prefixWord ++ tailWord_532170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532170).length < 2 ^ (prefixWord ++ tailWord_532170).sum := by decide
  have hdescent : baseEnd_532170 < baseStart_532170 := by decide
  rcases family_descends (prefixWord ++ tailWord_532170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532185 : List Nat := [1, 2, 1, 2, 3, 3, 8]
def baseStart_532185 : Nat := 118140960795 + 532185 * 2 ^ 59
def prefixEnd_532185 : Nat := 4983230072969 + 3 ^ 40 * 532185 * 2
def baseEnd_532185 : Nat := 26989303912405487154571

theorem tailTrace_532185 : CollatzResearch.WordTrace tailWord_532185 prefixEnd_532185 26989303912405487154571 := by
  unfold tailWord_532185
  simp only [CollatzResearch.WordTrace]
  refine ⟨19410381576992109806990009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12940254384661406537993339 19410381576992109806990009)
  ·
    refine ⟨14557786182744082355242507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19410381576992109806990009 14557786182744082355242507)
    ·
      refine ⟨21836679274116123532863761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14557786182744082355242507 21836679274116123532863761)
      ·
        refine ⟨16377509455587092649647821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21836679274116123532863761 16377509455587092649647821)
        ·
          refine ⟨6141566045845159743617933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16377509455587092649647821 6141566045845159743617933)
          ·
            refine ⟨2303087267191934903856725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6141566045845159743617933 2303087267191934903856725)
            ·
              refine ⟨26989303912405487154571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2303087267191934903856725 26989303912405487154571)
              ·
                rfl

theorem cell20_532185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 8].length) (baseStart_532185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532185 prefixEnd_532185 := by exact prefixLift 532185
  have htrace : WordTrace (prefixWord ++ tailWord_532185) baseStart_532185 baseEnd_532185 := by
    simpa [prefixWord, tailWord_532185, baseEnd_532185] using wordTrace_append hprefix tailTrace_532185
  have hstable : (prefixWord ++ tailWord_532185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532185).length < 2 ^ (prefixWord ++ tailWord_532185).sum := by decide
  have hdescent : baseEnd_532185 < baseStart_532185 := by decide
  rcases family_descends (prefixWord ++ tailWord_532185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532205 : List Nat := [1, 5, 1, 2, 1, 2, 4, 1, 3]
def baseStart_532205 : Nat := 118140960795 + 532205 * 2 ^ 59
def prefixEnd_532205 : Nat := 4983230072969 + 3 ^ 40 * 532205 * 2
def baseEnd_532205 : Nat := 242912863756618203724391

theorem tailTrace_532205 : CollatzResearch.WordTrace tailWord_532205 prefixEnd_532205 242912863756618203724391 := by
  unfold tailWord_532205
  simp only [CollatzResearch.WordTrace]
  refine ⟨19411111036919653222718069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12940740691279768815145379 19411111036919653222718069)
  ·
    refine ⟨1819791659711217489629819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19411111036919653222718069 1819791659711217489629819)
    ·
      refine ⟨2729687489566826234444729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1819791659711217489629819 2729687489566826234444729)
      ·
        refine ⟨2047265617175119675833547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2729687489566826234444729 2047265617175119675833547)
        ·
          refine ⟨3070898425762679513750321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2047265617175119675833547 3070898425762679513750321)
          ·
            refine ⟨2303173819322009635312741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3070898425762679513750321 2303173819322009635312741)
            ·
              refine ⟨431845091122876806621139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2303173819322009635312741 431845091122876806621139)
              ·
                refine ⟨647767636684315209931709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431845091122876806621139 647767636684315209931709)
                ·
                  refine ⟨242912863756618203724391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647767636684315209931709 242912863756618203724391)
                  ·
                    rfl

theorem cell20_532205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_532205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532205 prefixEnd_532205 := by exact prefixLift 532205
  have htrace : WordTrace (prefixWord ++ tailWord_532205) baseStart_532205 baseEnd_532205 := by
    simpa [prefixWord, tailWord_532205, baseEnd_532205] using wordTrace_append hprefix tailTrace_532205
  have hstable : (prefixWord ++ tailWord_532205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532205).length < 2 ^ (prefixWord ++ tailWord_532205).sum := by decide
  have hdescent : baseEnd_532205 < baseStart_532205 := by decide
  rcases family_descends (prefixWord ++ tailWord_532205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532223 : List Nat := [1, 1, 2, 2, 1, 3, 4, 6]
def baseStart_532223 : Nat := 118140960795 + 532223 * 2 ^ 59
def prefixEnd_532223 : Nat := 4983230072969 + 3 ^ 40 * 532223 * 2
def baseEnd_532223 : Nat := 80973693149030047041439

theorem tailTrace_532223 : CollatzResearch.WordTrace tailWord_532223 prefixEnd_532223 80973693149030047041439 := by
  unfold tailWord_532223
  simp only [CollatzResearch.WordTrace]
  refine ⟨19411767550854442296873323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12941178367236294864582215 19411767550854442296873323)
  ·
    refine ⟨29117651326281663445309985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19411767550854442296873323 29117651326281663445309985)
    ·
      refine ⟨21838238494711247583982489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29117651326281663445309985 21838238494711247583982489)
      ·
        refine ⟨16378678871033435687986867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21838238494711247583982489 16378678871033435687986867)
        ·
          refine ⟨24568018306550153531980301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16378678871033435687986867 24568018306550153531980301)
          ·
            refine ⟨9213006864956307574492613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24568018306550153531980301 9213006864956307574492613)
            ·
              refine ⟨1727438787179307670217365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9213006864956307574492613 1727438787179307670217365)
              ·
                refine ⟨80973693149030047041439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1727438787179307670217365 80973693149030047041439)
                ·
                  rfl

theorem cell20_532223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 6].length) (baseStart_532223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532223 prefixEnd_532223 := by exact prefixLift 532223
  have htrace : WordTrace (prefixWord ++ tailWord_532223) baseStart_532223 baseEnd_532223 := by
    simpa [prefixWord, tailWord_532223, baseEnd_532223] using wordTrace_append hprefix tailTrace_532223
  have hstable : (prefixWord ++ tailWord_532223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532223).length < 2 ^ (prefixWord ++ tailWord_532223).sum := by decide
  have hdescent : baseEnd_532223 < baseStart_532223 := by decide
  rcases family_descends (prefixWord ++ tailWord_532223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532233 : List Nat := [1, 2, 1, 1, 3, 2, 1, 7, 2]
def baseStart_532233 : Nat := 118140960795 + 532233 * 2 ^ 59
def prefixEnd_532233 : Nat := 4983230072969 + 3 ^ 40 * 532233 * 2
def baseEnd_532233 : Nat := 242925643719574550790943

theorem tailTrace_532233 : CollatzResearch.WordTrace tailWord_532233 prefixEnd_532233 242925643719574550790943 := by
  unfold tailWord_532233
  simp only [CollatzResearch.WordTrace]
  refine ⟨19412132280818214004737353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12941421520545476003158235 19412132280818214004737353)
  ·
    refine ⟨14559099210613660503553015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19412132280818214004737353 14559099210613660503553015)
    ·
      refine ⟨21838648815920490755329523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14559099210613660503553015 21838648815920490755329523)
      ·
        refine ⟨32757973223880736132994285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21838648815920490755329523 32757973223880736132994285)
        ·
          refine ⟨12284239958955276049872857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32757973223880736132994285 12284239958955276049872857)
          ·
            refine ⟨9213179969216457037404643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12284239958955276049872857 9213179969216457037404643)
            ·
              refine ⟨13819769953824685556106965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9213179969216457037404643 13819769953824685556106965)
              ·
                refine ⟨323900858292766067721257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13819769953824685556106965 323900858292766067721257)
                ·
                  refine ⟨242925643719574550790943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323900858292766067721257 242925643719574550790943)
                  ·
                    rfl

theorem cell20_532233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 2].length) (baseStart_532233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532233 prefixEnd_532233 := by exact prefixLift 532233
  have htrace : WordTrace (prefixWord ++ tailWord_532233) baseStart_532233 baseEnd_532233 := by
    simpa [prefixWord, tailWord_532233, baseEnd_532233] using wordTrace_append hprefix tailTrace_532233
  have hstable : (prefixWord ++ tailWord_532233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532233).length < 2 ^ (prefixWord ++ tailWord_532233).sum := by decide
  have hdescent : baseEnd_532233 < baseStart_532233 := by decide
  rcases family_descends (prefixWord ++ tailWord_532233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532250 : List Nat := [3, 1, 1, 3, 2, 3, 1, 4, 2]
def baseStart_532250 : Nat := 118140960795 + 532250 * 2 ^ 59
def prefixEnd_532250 : Nat := 4983230072969 + 3 ^ 40 * 532250 * 2
def baseEnd_532250 : Nat := 242933402982798047224207

theorem tailTrace_532250 : CollatzResearch.WordTrace tailWord_532250 prefixEnd_532250 242933402982798047224207 := by
  unfold tailWord_532250
  simp only [CollatzResearch.WordTrace]
  refine ⟨4853188080439156477026551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12941834881171083938737469 4853188080439156477026551)
  ·
    refine ⟨7279782120658734715539827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4853188080439156477026551 7279782120658734715539827)
    ·
      refine ⟨10919673180988102073309741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7279782120658734715539827 10919673180988102073309741)
      ·
        refine ⟨4094877442870538277491153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10919673180988102073309741 4094877442870538277491153)
        ·
          refine ⟨3071158082152903708118365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4094877442870538277491153 3071158082152903708118365)
          ·
            refine ⟨1151684280807338890544387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3071158082152903708118365 1151684280807338890544387)
            ·
              refine ⟨1727526421211008335816581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1151684280807338890544387 1727526421211008335816581)
              ·
                refine ⟨323911203977064062965609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1727526421211008335816581 323911203977064062965609)
                ·
                  refine ⟨242933402982798047224207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323911203977064062965609 242933402982798047224207)
                  ·
                    rfl

theorem cell20_532250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_532250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532250 prefixEnd_532250 := by exact prefixLift 532250
  have htrace : WordTrace (prefixWord ++ tailWord_532250) baseStart_532250 baseEnd_532250 := by
    simpa [prefixWord, tailWord_532250, baseEnd_532250] using wordTrace_append hprefix tailTrace_532250
  have hstable : (prefixWord ++ tailWord_532250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532250).length < 2 ^ (prefixWord ++ tailWord_532250).sum := by decide
  have hdescent : baseEnd_532250 < baseStart_532250 := by decide
  rcases family_descends (prefixWord ++ tailWord_532250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532264 : List Nat := [2, 1, 5, 1, 1, 2, 2, 3, 3]
def baseStart_532264 : Nat := 118140960795 + 532264 * 2 ^ 59
def prefixEnd_532264 : Nat := 4983230072969 + 3 ^ 40 * 532264 * 2
def baseEnd_532264 : Nat := 242939792964276220757483

theorem tailTrace_532264 : CollatzResearch.WordTrace tailWord_532264 prefixEnd_532264 242939792964276220757483 := by
  unfold tailWord_532264
  simp only [CollatzResearch.WordTrace]
  refine ⟨9706631471852953149557923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12942175295803937532743897 9706631471852953149557923)
  ·
    refine ⟨14559947207779429724336885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9706631471852953149557923 14559947207779429724336885)
    ·
      refine ⟨1364995050729321536656583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14559947207779429724336885 1364995050729321536656583)
      ·
        refine ⟨2047492576093982304984875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1364995050729321536656583 2047492576093982304984875)
        ·
          refine ⟨3071238864140973457477313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2047492576093982304984875 3071238864140973457477313)
          ·
            refine ⟨2303429148105730093107985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3071238864140973457477313 2303429148105730093107985)
            ·
              refine ⟨1727571861079297569830989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2303429148105730093107985 1727571861079297569830989)
              ·
                refine ⟨647839447904736588686621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1727571861079297569830989 647839447904736588686621)
                ·
                  refine ⟨242939792964276220757483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647839447904736588686621 242939792964276220757483)
                  ·
                    rfl

theorem cell20_532264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_532264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532264 prefixEnd_532264 := by exact prefixLift 532264
  have htrace : WordTrace (prefixWord ++ tailWord_532264) baseStart_532264 baseEnd_532264 := by
    simpa [prefixWord, tailWord_532264, baseEnd_532264] using wordTrace_append hprefix tailTrace_532264
  have hstable : (prefixWord ++ tailWord_532264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532264).length < 2 ^ (prefixWord ++ tailWord_532264).sum := by decide
  have hdescent : baseEnd_532264 < baseStart_532264 := by decide
  rcases family_descends (prefixWord ++ tailWord_532264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532309 : List Nat := [1, 3, 2, 2, 2, 3, 2, 1, 4]
def baseStart_532309 : Nat := 118140960795 + 532309 * 2 ^ 59
def prefixEnd_532309 : Nat := 4983230072969 + 3 ^ 40 * 532309 * 2
def baseEnd_532309 : Nat := 242960332190456064257299

theorem tailTrace_532309 : CollatzResearch.WordTrace tailWord_532309 prefixEnd_532309 242960332190456064257299 := by
  unfold tailWord_532309
  simp only [CollatzResearch.WordTrace]
  refine ⟨19414904228542878984503981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12943269485695252656335987 19414904228542878984503981)
  ·
    refine ⟨7280589085703579619188993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19414904228542878984503981 7280589085703579619188993)
    ·
      refine ⟨5460441814277684714391745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7280589085703579619188993 5460441814277684714391745)
      ·
        refine ⟨4095331360708263535793809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5460441814277684714391745 4095331360708263535793809)
        ·
          refine ⟨3071498520531197651845357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4095331360708263535793809 3071498520531197651845357)
          ·
            refine ⟨1151811945199199119442009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3071498520531197651845357 1151811945199199119442009)
            ·
              refine ⟨863858958899399339581507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1151811945199199119442009 863858958899399339581507)
              ·
                refine ⟨1295788438349099009372261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863858958899399339581507 1295788438349099009372261)
                ·
                  refine ⟨242960332190456064257299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1295788438349099009372261 242960332190456064257299)
                  ·
                    rfl

theorem cell20_532309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_532309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532309 prefixEnd_532309 := by exact prefixLift 532309
  have htrace : WordTrace (prefixWord ++ tailWord_532309) baseStart_532309 baseEnd_532309 := by
    simpa [prefixWord, tailWord_532309, baseEnd_532309] using wordTrace_append hprefix tailTrace_532309
  have hstable : (prefixWord ++ tailWord_532309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532309).length < 2 ^ (prefixWord ++ tailWord_532309).sum := by decide
  have hdescent : baseEnd_532309 < baseStart_532309 := by decide
  rcases family_descends (prefixWord ++ tailWord_532309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532337 : List Nat := [1, 2, 2, 2, 1, 3, 3, 6]
def baseStart_532337 : Nat := 118140960795 + 532337 * 2 ^ 59
def prefixEnd_532337 : Nat := 4983230072969 + 3 ^ 40 * 532337 * 2
def baseEnd_532337 : Nat := 80991037384470803774617

theorem tailTrace_532337 : CollatzResearch.WordTrace tailWord_532337 prefixEnd_532337 80991037384470803774617 := by
  unfold tailWord_532337
  simp only [CollatzResearch.WordTrace]
  refine ⟨19415925472441439766523265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12943950314960959844348843 19415925472441439766523265)
  ·
    refine ⟨14561944104331079824892449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19415925472441439766523265 14561944104331079824892449)
    ·
      refine ⟨10921458078248309868669337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14561944104331079824892449 10921458078248309868669337)
      ·
        refine ⟨8191093558686232401502003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10921458078248309868669337 8191093558686232401502003)
        ·
          refine ⟨12286640338029348602253005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8191093558686232401502003 12286640338029348602253005)
          ·
            refine ⟨4607490126761005725844877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12286640338029348602253005 4607490126761005725844877)
            ·
              refine ⟨1727808797535377147191829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4607490126761005725844877 1727808797535377147191829)
              ·
                refine ⟨80991037384470803774617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1727808797535377147191829 80991037384470803774617)
                ·
                  rfl

theorem cell20_532337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 6].length) (baseStart_532337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532337 prefixEnd_532337 := by exact prefixLift 532337
  have htrace : WordTrace (prefixWord ++ tailWord_532337) baseStart_532337 baseEnd_532337 := by
    simpa [prefixWord, tailWord_532337, baseEnd_532337] using wordTrace_append hprefix tailTrace_532337
  have hstable : (prefixWord ++ tailWord_532337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532337).length < 2 ^ (prefixWord ++ tailWord_532337).sum := by decide
  have hdescent : baseEnd_532337 < baseStart_532337 := by decide
  rcases family_descends (prefixWord ++ tailWord_532337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532361 : List Nat := [1, 2, 1, 1, 5, 1, 2, 4, 3]
def baseStart_532361 : Nat := 118140960795 + 532361 * 2 ^ 59
def prefixEnd_532361 : Nat := 4983230072969 + 3 ^ 40 * 532361 * 2
def baseEnd_532361 : Nat := 242984066407374994523753

theorem tailTrace_532361 : CollatzResearch.WordTrace tailWord_532361 prefixEnd_532361 242984066407374994523753 := by
  unfold tailWord_532361
  simp only [CollatzResearch.WordTrace]
  refine ⟨19416800824354491865396937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12944533882902994576931291 19416800824354491865396937)
  ·
    refine ⟨14562600618265868899047703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19416800824354491865396937 14562600618265868899047703)
    ·
      refine ⟨21843900927398803348571555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14562600618265868899047703 21843900927398803348571555)
      ·
        refine ⟨32765851391098205022857333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21843900927398803348571555 32765851391098205022857333)
        ·
          refine ⟨3071798567915456720892875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32765851391098205022857333 3071798567915456720892875)
          ·
            refine ⟨4607697851873185081339313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3071798567915456720892875 4607697851873185081339313)
            ·
              refine ⟨3455773388904888811004485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4607697851873185081339313 3455773388904888811004485)
              ·
                refine ⟨647957510419666652063341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3455773388904888811004485 647957510419666652063341)
                ·
                  refine ⟨242984066407374994523753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647957510419666652063341 242984066407374994523753)
                  ·
                    rfl

theorem cell20_532361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_532361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532361 prefixEnd_532361 := by exact prefixLift 532361
  have htrace : WordTrace (prefixWord ++ tailWord_532361) baseStart_532361 baseEnd_532361 := by
    simpa [prefixWord, tailWord_532361, baseEnd_532361] using wordTrace_append hprefix tailTrace_532361
  have hstable : (prefixWord ++ tailWord_532361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532361).length < 2 ^ (prefixWord ++ tailWord_532361).sum := by decide
  have hdescent : baseEnd_532361 < baseStart_532361 := by decide
  rcases family_descends (prefixWord ++ tailWord_532361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532375 : List Nat := [1, 1, 3, 3, 1, 3, 1, 7]
def baseStart_532375 : Nat := 118140960795 + 532375 * 2 ^ 59
def prefixEnd_532375 : Nat := 4983230072969 + 3 ^ 40 * 532375 * 2
def baseEnd_532375 : Nat := 80996818796284389352343

theorem tailTrace_532375 : CollatzResearch.WordTrace tailWord_532375 prefixEnd_532375 80996818796284389352343 := by
  unfold tailWord_532375
  simp only [CollatzResearch.WordTrace]
  refine ⟨19417311446303772256406579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12944874297535848170937719 19417311446303772256406579)
  ·
    refine ⟨29125967169455658384609869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19417311446303772256406579 29125967169455658384609869)
    ·
      refine ⟨10922237688545871894228701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29125967169455658384609869 10922237688545871894228701)
      ·
        refine ⟨4095839133204701960335763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10922237688545871894228701 4095839133204701960335763)
        ·
          refine ⟨6143758699807052940503645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4095839133204701960335763 6143758699807052940503645)
          ·
            refine ⟨2303909512427644852688867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6143758699807052940503645 2303909512427644852688867)
            ·
              refine ⟨3455864268641467279033301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2303909512427644852688867 3455864268641467279033301)
              ·
                refine ⟨80996818796284389352343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3455864268641467279033301 80996818796284389352343)
                ·
                  rfl

theorem cell20_532375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 7].length) (baseStart_532375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532375 prefixEnd_532375 := by exact prefixLift 532375
  have htrace : WordTrace (prefixWord ++ tailWord_532375) baseStart_532375 baseEnd_532375 := by
    simpa [prefixWord, tailWord_532375, baseEnd_532375] using wordTrace_append hprefix tailTrace_532375
  have hstable : (prefixWord ++ tailWord_532375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532375).length < 2 ^ (prefixWord ++ tailWord_532375).sum := by decide
  have hdescent : baseEnd_532375 < baseStart_532375 := by decide
  rcases family_descends (prefixWord ++ tailWord_532375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532378 : List Nat := [3, 1, 1, 4, 2, 2, 1, 3, 3]
def baseStart_532378 : Nat := 118140960795 + 532378 * 2 ^ 59
def prefixEnd_532378 : Nat := 4983230072969 + 3 ^ 40 * 532378 * 2
def baseEnd_532378 : Nat := 242991825670598490957017

theorem tailTrace_532378 : CollatzResearch.WordTrace tailWord_532378 prefixEnd_532378 242991825670598490957017 := by
  unfold tailWord_532378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4854355216323225942191447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12944947243528602512510525 4854355216323225942191447)
  ·
    refine ⟨7281532824484838913287171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4854355216323225942191447 7281532824484838913287171)
    ·
      refine ⟨10922299236727258369930757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7281532824484838913287171 10922299236727258369930757)
      ·
        refine ⟨2047931106886360944362017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10922299236727258369930757 2047931106886360944362017)
        ·
          refine ⟨1535948330164770708271513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2047931106886360944362017 1535948330164770708271513)
          ·
            refine ⟨1151961247623578031203635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1535948330164770708271513 1151961247623578031203635)
            ·
              refine ⟨1727941871435367046805453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1151961247623578031203635 1727941871435367046805453)
              ·
                refine ⟨647978201788262642552045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1727941871435367046805453 647978201788262642552045)
                ·
                  refine ⟨242991825670598490957017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647978201788262642552045 242991825670598490957017)
                  ·
                    rfl

theorem cell20_532378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_532378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532378 prefixEnd_532378 := by exact prefixLift 532378
  have htrace : WordTrace (prefixWord ++ tailWord_532378) baseStart_532378 baseEnd_532378 := by
    simpa [prefixWord, tailWord_532378, baseEnd_532378] using wordTrace_append hprefix tailTrace_532378
  have hstable : (prefixWord ++ tailWord_532378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532378).length < 2 ^ (prefixWord ++ tailWord_532378).sum := by decide
  have hdescent : baseEnd_532378 < baseStart_532378 := by decide
  rcases family_descends (prefixWord ++ tailWord_532378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532413 : List Nat := [1, 4, 1, 2, 3, 9]
def baseStart_532413 : Nat := 118140960795 + 532413 * 2 ^ 59
def prefixEnd_532413 : Nat := 4983230072969 + 3 ^ 40 * 532413 * 2
def baseEnd_532413 : Nat := 9000288912010886103341

theorem tailTrace_532413 : CollatzResearch.WordTrace tailWord_532413 prefixEnd_532413 9000288912010886103341 := by
  unfold tailWord_532413
  simp only [CollatzResearch.WordTrace]
  refine ⟨19418697420166104746289893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12945798280110736497526595 19418697420166104746289893)
  ·
    refine ⟨3641005766281144639929355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19418697420166104746289893 3641005766281144639929355)
    ·
      refine ⟨5461508649421716959894033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3641005766281144639929355 5461508649421716959894033)
      ·
        refine ⟨4096131487066287719920525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5461508649421716959894033 4096131487066287719920525)
        ·
          refine ⟨1536049307649857894970197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4096131487066287719920525 1536049307649857894970197)
          ·
            refine ⟨9000288912010886103341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1536049307649857894970197 9000288912010886103341)
            ·
              rfl

theorem cell20_532413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 9].length) (baseStart_532413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532413 prefixEnd_532413 := by exact prefixLift 532413
  have htrace : WordTrace (prefixWord ++ tailWord_532413) baseStart_532413 baseEnd_532413 := by
    simpa [prefixWord, tailWord_532413, baseEnd_532413] using wordTrace_append hprefix tailTrace_532413
  have hstable : (prefixWord ++ tailWord_532413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532413).length < 2 ^ (prefixWord ++ tailWord_532413).sum := by decide
  have hdescent : baseEnd_532413 < baseStart_532413 := by decide
  rcases family_descends (prefixWord ++ tailWord_532413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532475 : List Nat := [1, 1, 1, 1, 1, 3, 7, 2, 3]
def baseStart_532475 : Nat := 118140960795 + 532475 * 2 ^ 59
def prefixEnd_532475 : Nat := 4983230072969 + 3 ^ 40 * 532475 * 2
def baseEnd_532475 : Nat := 243036099113697264723287

theorem tailTrace_532475 : CollatzResearch.WordTrace tailWord_532475 prefixEnd_532475 243036099113697264723287 := by
  unfold tailWord_532475
  simp only [CollatzResearch.WordTrace]
  refine ⟨19420958745941489335046879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12947305830627659556697919 19420958745941489335046879)
  ·
    refine ⟨29131438118912234002570319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19420958745941489335046879 29131438118912234002570319)
    ·
      refine ⟨43697157178368351003855479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29131438118912234002570319 43697157178368351003855479)
      ·
        refine ⟨65545735767552526505783219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43697157178368351003855479 65545735767552526505783219)
        ·
          refine ⟨98318603651328789758674829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65545735767552526505783219 98318603651328789758674829)
          ·
            refine ⟨36869476369248296159503061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98318603651328789758674829 36869476369248296159503061)
            ·
              refine ⟨864128352404256941238353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 36869476369248296159503061 864128352404256941238353)
              ·
                refine ⟨648096264303192705928765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864128352404256941238353 648096264303192705928765)
                ·
                  refine ⟨243036099113697264723287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 648096264303192705928765 243036099113697264723287)
                  ·
                    rfl

theorem cell20_532475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 3].length) (baseStart_532475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532475 prefixEnd_532475 := by exact prefixLift 532475
  have htrace : WordTrace (prefixWord ++ tailWord_532475) baseStart_532475 baseEnd_532475 := by
    simpa [prefixWord, tailWord_532475, baseEnd_532475] using wordTrace_append hprefix tailTrace_532475
  have hstable : (prefixWord ++ tailWord_532475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532475).length < 2 ^ (prefixWord ++ tailWord_532475).sum := by decide
  have hdescent : baseEnd_532475 < baseStart_532475 := by decide
  rcases family_descends (prefixWord ++ tailWord_532475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532478 : List Nat := [4, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_532478 : Nat := 118140960795 + 532478 * 2 ^ 59
def prefixEnd_532478 : Nat := 4983230072969 + 3 ^ 40 * 532478 * 2
def baseEnd_532478 : Nat := 243037468395442587623275

theorem tailTrace_532478 : CollatzResearch.WordTrace tailWord_532478 prefixEnd_532478 243037468395442587623275 := by
  unfold tailWord_532478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2427633520616327605925761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12947378776620413898270725 2427633520616327605925761)
  ·
    refine ⟨1820725140462245704444321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2427633520616327605925761 1820725140462245704444321)
    ·
      refine ⟨1365543855346684278333241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1820725140462245704444321 1365543855346684278333241)
      ·
        refine ⟨1024157891510013208749931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1365543855346684278333241 1024157891510013208749931)
        ·
          refine ⟨1536236837265019813124897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1024157891510013208749931 1536236837265019813124897)
          ·
            refine ⟨1152177627948764859843673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1536236837265019813124897 1152177627948764859843673)
            ·
              refine ⟨864133220961573644882755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1152177627948764859843673 864133220961573644882755)
              ·
                refine ⟨1296199831442360467324133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 864133220961573644882755 1296199831442360467324133)
                ·
                  refine ⟨243037468395442587623275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1296199831442360467324133 243037468395442587623275)
                  ·
                    rfl

theorem cell20_532478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_532478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532478 prefixEnd_532478 := by exact prefixLift 532478
  have htrace : WordTrace (prefixWord ++ tailWord_532478) baseStart_532478 baseEnd_532478 := by
    simpa [prefixWord, tailWord_532478, baseEnd_532478] using wordTrace_append hprefix tailTrace_532478
  have hstable : (prefixWord ++ tailWord_532478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532478).length < 2 ^ (prefixWord ++ tailWord_532478).sum := by decide
  have hdescent : baseEnd_532478 < baseStart_532478 := by decide
  rcases family_descends (prefixWord ++ tailWord_532478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532492 : List Nat := [2, 2, 1, 2, 3, 1, 5, 1, 3]
def baseStart_532492 : Nat := 118140960795 + 532492 * 2 ^ 59
def prefixEnd_532492 : Nat := 4983230072969 + 3 ^ 40 * 532492 * 2
def baseEnd_532492 : Nat := 243043858376920761156551

theorem tailTrace_532492 : CollatzResearch.WordTrace tailWord_532492 prefixEnd_532492 243043858376920761156551 := by
  unfold tailWord_532492
  simp only [CollatzResearch.WordTrace]
  refine ⟨9710789393439950619207865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12947719191253267492277153 9710789393439950619207865)
  ·
    refine ⟨7283092045079962964405899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9710789393439950619207865 7283092045079962964405899)
    ·
      refine ⟨10924638067619944446608849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7283092045079962964405899 10924638067619944446608849)
      ·
        refine ⟨8193478550714958334956637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10924638067619944446608849 8193478550714958334956637)
        ·
          refine ⟨3072554456518109375608739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8193478550714958334956637 3072554456518109375608739)
          ·
            refine ⟨4608831684777164063413109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3072554456518109375608739 4608831684777164063413109)
            ·
              refine ⟨432077970447859130944979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4608831684777164063413109 432077970447859130944979)
              ·
                refine ⟨648116955671788696417469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432077970447859130944979 648116955671788696417469)
                ·
                  refine ⟨243043858376920761156551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 648116955671788696417469 243043858376920761156551)
                  ·
                    rfl

theorem cell20_532492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_532492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532492 prefixEnd_532492 := by exact prefixLift 532492
  have htrace : WordTrace (prefixWord ++ tailWord_532492) baseStart_532492 baseEnd_532492 := by
    simpa [prefixWord, tailWord_532492, baseEnd_532492] using wordTrace_append hprefix tailTrace_532492
  have hstable : (prefixWord ++ tailWord_532492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532492).length < 2 ^ (prefixWord ++ tailWord_532492).sum := by decide
  have hdescent : baseEnd_532492 < baseStart_532492 := by decide
  rcases family_descends (prefixWord ++ tailWord_532492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532506 : List Nat := [3, 1, 1, 3, 1, 3, 4, 4]
def baseStart_532506 : Nat := 118140960795 + 532506 * 2 ^ 59
def prefixEnd_532506 : Nat := 4983230072969 + 3 ^ 40 * 532506 * 2
def baseEnd_532506 : Nat := 81016749452799644896609

theorem tailTrace_532506 : CollatzResearch.WordTrace tailWord_532506 prefixEnd_532506 81016749452799644896609 := by
  unfold tailWord_532506
  simp only [CollatzResearch.WordTrace]
  refine ⟨4855522352207295407356343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12948059605886121086283581 4855522352207295407356343)
  ·
    refine ⟨7283283528310943111034515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4855522352207295407356343 7283283528310943111034515)
    ·
      refine ⟨10924925292466414666551773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7283283528310943111034515 10924925292466414666551773)
      ·
        refine ⟨4096846984674905499956915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10924925292466414666551773 4096846984674905499956915)
        ·
          refine ⟨6145270477012358249935373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4096846984674905499956915 6145270477012358249935373)
          ·
            refine ⟨2304476428879634343725765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6145270477012358249935373 2304476428879634343725765)
            ·
              refine ⟨432089330414931439448581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2304476428879634343725765 432089330414931439448581)
              ·
                refine ⟨81016749452799644896609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 432089330414931439448581 81016749452799644896609)
                ·
                  rfl

theorem cell20_532506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_532506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532506 prefixEnd_532506 := by exact prefixLift 532506
  have htrace : WordTrace (prefixWord ++ tailWord_532506) baseStart_532506 baseEnd_532506 := by
    simpa [prefixWord, tailWord_532506, baseEnd_532506] using wordTrace_append hprefix tailTrace_532506
  have hstable : (prefixWord ++ tailWord_532506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532506).length < 2 ^ (prefixWord ++ tailWord_532506).sum := by decide
  have hdescent : baseEnd_532506 < baseStart_532506 := by decide
  rcases family_descends (prefixWord ++ tailWord_532506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532551 : List Nat := [1, 1, 4, 1, 3, 1, 3, 3, 3]
def baseStart_532551 : Nat := 118140960795 + 532551 * 2 ^ 59
def prefixEnd_532551 : Nat := 4983230072969 + 3 ^ 40 * 532551 * 2
def baseEnd_532551 : Nat := 243070787584578778189643

theorem tailTrace_532551 : CollatzResearch.WordTrace tailWord_532551 prefixEnd_532551 243070787584578778189643 := by
  unfold tailWord_532551
  simp only [CollatzResearch.WordTrace]
  refine ⟨19423730693666154314813507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12949153795777436209875671 19423730693666154314813507)
  ·
    refine ⟨29135596040499231472220261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19423730693666154314813507 29135596040499231472220261)
    ·
      refine ⟨5462924257593605901041299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29135596040499231472220261 5462924257593605901041299)
      ·
        refine ⟨8194386386390408851561949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5462924257593605901041299 8194386386390408851561949)
        ·
          refine ⟨3072894894896403319335731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8194386386390408851561949 3072894894896403319335731)
          ·
            refine ⟨4609342342344604979003597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3072894894896403319335731 4609342342344604979003597)
            ·
              refine ⟨1728503378379226867126349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4609342342344604979003597 1728503378379226867126349)
              ·
                refine ⟨648188766892210075172381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1728503378379226867126349 648188766892210075172381)
                ·
                  refine ⟨243070787584578778189643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 648188766892210075172381 243070787584578778189643)
                  ·
                    rfl

theorem cell20_532551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 3].length) (baseStart_532551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532551 prefixEnd_532551 := by exact prefixLift 532551
  have htrace : WordTrace (prefixWord ++ tailWord_532551) baseStart_532551 baseEnd_532551 := by
    simpa [prefixWord, tailWord_532551, baseEnd_532551] using wordTrace_append hprefix tailTrace_532551
  have hstable : (prefixWord ++ tailWord_532551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532551).length < 2 ^ (prefixWord ++ tailWord_532551).sum := by decide
  have hdescent : baseEnd_532551 < baseStart_532551 := by decide
  rcases family_descends (prefixWord ++ tailWord_532551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532565 : List Nat := [1, 3, 2, 2, 1, 3, 2, 6]
def baseStart_532565 : Nat := 118140960795 + 532565 * 2 ^ 59
def prefixEnd_532565 : Nat := 4983230072969 + 3 ^ 40 * 532565 * 2
def baseEnd_532565 : Nat := 81025725855352317240973

theorem tailTrace_532565 : CollatzResearch.WordTrace tailWord_532565 prefixEnd_532565 81025725855352317240973 := by
  unfold tailWord_532565
  simp only [CollatzResearch.WordTrace]
  refine ⟨19424241315615434705823149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12949494210410289803882099 19424241315615434705823149)
  ·
    refine ⟨7284090493355788014683681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19424241315615434705823149 7284090493355788014683681)
    ·
      refine ⟨5463067870016841011012761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7284090493355788014683681 5463067870016841011012761)
      ·
        refine ⟨4097300902512630758259571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5463067870016841011012761 4097300902512630758259571)
        ·
          refine ⟨6145951353768946137389357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4097300902512630758259571 6145951353768946137389357)
          ·
            refine ⟨2304731757663354801521009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6145951353768946137389357 2304731757663354801521009)
            ·
              refine ⟨1728548818247516101140757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2304731757663354801521009 1728548818247516101140757)
              ·
                refine ⟨81025725855352317240973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1728548818247516101140757 81025725855352317240973)
                ·
                  rfl

theorem cell20_532565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 6].length) (baseStart_532565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532565 prefixEnd_532565 := by exact prefixLift 532565
  have htrace : WordTrace (prefixWord ++ tailWord_532565) baseStart_532565 baseEnd_532565 := by
    simpa [prefixWord, tailWord_532565, baseEnd_532565] using wordTrace_append hprefix tailTrace_532565
  have hstable : (prefixWord ++ tailWord_532565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532565).length < 2 ^ (prefixWord ++ tailWord_532565).sum := by decide
  have hdescent : baseEnd_532565 < baseStart_532565 := by decide
  rcases family_descends (prefixWord ++ tailWord_532565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532592 : List Nat := [2, 1, 1, 1, 5, 2, 4, 2, 2]
def baseStart_532592 : Nat := 118140960795 + 532592 * 2 ^ 59
def prefixEnd_532592 : Nat := 4983230072969 + 3 ^ 40 * 532592 * 2
def baseEnd_532592 : Nat := 243089501101764857822809

theorem tailTrace_532592 : CollatzResearch.WordTrace tailWord_532592 prefixEnd_532592 243089501101764857822809 := by
  unfold tailWord_532592
  simp only [CollatzResearch.WordTrace]
  refine ⟨9712613043258809158528015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12950150724345078878037353 9712613043258809158528015)
  ·
    refine ⟨14568919564888213737792023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9712613043258809158528015 14568919564888213737792023)
    ·
      refine ⟨21853379347332320606688035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14568919564888213737792023 21853379347332320606688035)
      ·
        refine ⟨32780069020998480910032053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21853379347332320606688035 32780069020998480910032053)
        ·
          refine ⟨3073131470718607585315505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32780069020998480910032053 3073131470718607585315505)
          ·
            refine ⟨2304848603038955688986629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3073131470718607585315505 2304848603038955688986629)
            ·
              refine ⟨432159113069804191684993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2304848603038955688986629 432159113069804191684993)
              ·
                refine ⟨324119334802353143763745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432159113069804191684993 324119334802353143763745)
                ·
                  refine ⟨243089501101764857822809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324119334802353143763745 243089501101764857822809)
                  ·
                    rfl

theorem cell20_532592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 2].length) (baseStart_532592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532592 prefixEnd_532592 := by exact prefixLift 532592
  have htrace : WordTrace (prefixWord ++ tailWord_532592) baseStart_532592 baseEnd_532592 := by
    simpa [prefixWord, tailWord_532592, baseEnd_532592] using wordTrace_append hprefix tailTrace_532592
  have hstable : (prefixWord ++ tailWord_532592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532592).length < 2 ^ (prefixWord ++ tailWord_532592).sum := by decide
  have hdescent : baseEnd_532592 < baseStart_532592 := by decide
  rcases family_descends (prefixWord ++ tailWord_532592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532641 : List Nat := [1, 2, 3, 3, 1, 3, 7]
def baseStart_532641 : Nat := 118140960795 + 532641 * 2 ^ 59
def prefixEnd_532641 : Nat := 4983230072969 + 3 ^ 40 * 532641 * 2
def baseEnd_532641 : Nat := 27012429559659829465475

theorem tailTrace_532641 : CollatzResearch.WordTrace tailWord_532641 prefixEnd_532641 27012429559659829465475 := by
  unfold tailWord_532641
  simp only [CollatzResearch.WordTrace]
  refine ⟨19427013263340099685589777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12951342175560066457059851 19427013263340099685589777)
  ·
    refine ⟨14570259947505074764192333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19427013263340099685589777 14570259947505074764192333)
    ·
      refine ⟨5463847480314403036572125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14570259947505074764192333 5463847480314403036572125)
      ·
        refine ⟨2048942805117901138714547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5463847480314403036572125 2048942805117901138714547)
        ·
          refine ⟨3073414207676851708071821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2048942805117901138714547 3073414207676851708071821)
          ·
            refine ⟨1152530327878819390526933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3073414207676851708071821 1152530327878819390526933)
            ·
              refine ⟨27012429559659829465475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1152530327878819390526933 27012429559659829465475)
              ·
                rfl

theorem cell20_532641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 7].length) (baseStart_532641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532641 prefixEnd_532641 := by exact prefixLift 532641
  have htrace : WordTrace (prefixWord ++ tailWord_532641) baseStart_532641 baseEnd_532641 := by
    simpa [prefixWord, tailWord_532641, baseEnd_532641] using wordTrace_append hprefix tailTrace_532641
  have hstable : (prefixWord ++ tailWord_532641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532641).length < 2 ^ (prefixWord ++ tailWord_532641).sum := by decide
  have hdescent : baseEnd_532641 < baseStart_532641 := by decide
  rcases family_descends (prefixWord ++ tailWord_532641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532672 : List Nat := [2, 1, 1, 2, 5, 1, 2, 2, 4]
def baseStart_532672 : Nat := 118140960795 + 532672 * 2 ^ 59
def prefixEnd_532672 : Nat := 4983230072969 + 3 ^ 40 * 532672 * 2
def baseEnd_532672 : Nat := 243126015281640135155815

theorem tailTrace_532672 : CollatzResearch.WordTrace tailWord_532672 prefixEnd_532672 243126015281640135155815 := by
  unfold tailWord_532672
  simp only [CollatzResearch.WordTrace]
  refine ⟨9714071963113895989984135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12952095950818527986645513 9714071963113895989984135)
  ·
    refine ⟨14571107944670843984976203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9714071963113895989984135 14571107944670843984976203)
    ·
      refine ⟨21856661917006265977464305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14571107944670843984976203 21856661917006265977464305)
      ·
        refine ⟨16392496437754699483098229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21856661917006265977464305 16392496437754699483098229)
        ·
          refine ⟨1536796541039503076540459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16392496437754699483098229 1536796541039503076540459)
          ·
            refine ⟨2305194811559254614810689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1536796541039503076540459 2305194811559254614810689)
            ·
              refine ⟨1728896108669440961108017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2305194811559254614810689 1728896108669440961108017)
              ·
                refine ⟨1296672081502080720831013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1728896108669440961108017 1296672081502080720831013)
                ·
                  refine ⟨243126015281640135155815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1296672081502080720831013 243126015281640135155815)
                  ·
                    rfl

theorem cell20_532672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_532672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532672 prefixEnd_532672 := by exact prefixLift 532672
  have htrace : WordTrace (prefixWord ++ tailWord_532672) baseStart_532672 baseEnd_532672 := by
    simpa [prefixWord, tailWord_532672, baseEnd_532672] using wordTrace_append hprefix tailTrace_532672
  have hstable : (prefixWord ++ tailWord_532672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532672).length < 2 ^ (prefixWord ++ tailWord_532672).sum := by decide
  have hdescent : baseEnd_532672 < baseStart_532672 := by decide
  rcases family_descends (prefixWord ++ tailWord_532672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532689 : List Nat := [1, 2, 2, 1, 2, 2, 5, 3, 2]
def baseStart_532689 : Nat := 118140960795 + 532689 * 2 ^ 59
def prefixEnd_532689 : Nat := 4983230072969 + 3 ^ 40 * 532689 * 2
def baseEnd_532689 : Nat := 243133774544863631589079

theorem tailTrace_532689 : CollatzResearch.WordTrace tailWord_532689 prefixEnd_532689 243133774544863631589079 := by
  unfold tailWord_532689
  simp only [CollatzResearch.WordTrace]
  refine ⟨19428763967166203883337121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12952509311444135922224747 19428763967166203883337121)
  ·
    refine ⟨14571572975374652912502841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19428763967166203883337121 14571572975374652912502841)
    ·
      refine ⟨10928679731530989684377131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14571572975374652912502841 10928679731530989684377131)
      ·
        refine ⟨16393019597296484526565697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10928679731530989684377131 16393019597296484526565697)
        ·
          refine ⟨12294764697972363394924273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16393019597296484526565697 12294764697972363394924273)
          ·
            refine ⟨9221073523479272546193205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12294764697972363394924273 9221073523479272546193205)
            ·
              refine ⟨864475642826181801205613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9221073523479272546193205 864475642826181801205613)
              ·
                refine ⟨324178366059818175452105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 864475642826181801205613 324178366059818175452105)
                ·
                  refine ⟨243133774544863631589079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324178366059818175452105 243133774544863631589079)
                  ·
                    rfl

theorem cell20_532689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 2].length) (baseStart_532689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532689 prefixEnd_532689 := by exact prefixLift 532689
  have htrace : WordTrace (prefixWord ++ tailWord_532689) baseStart_532689 baseEnd_532689 := by
    simpa [prefixWord, tailWord_532689, baseEnd_532689] using wordTrace_append hprefix tailTrace_532689
  have hstable : (prefixWord ++ tailWord_532689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532689).length < 2 ^ (prefixWord ++ tailWord_532689).sum := by decide
  have hdescent : baseEnd_532689 < baseStart_532689 := by decide
  rcases family_descends (prefixWord ++ tailWord_532689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532772 : List Nat := [2, 3, 1, 3, 1, 4, 1, 5]
def baseStart_532772 : Nat := 118140960795 + 532772 * 2 ^ 59
def prefixEnd_532772 : Nat := 4983230072969 + 3 ^ 40 * 532772 * 2
def baseEnd_532772 : Nat := 81057219335494743940691

theorem tailTrace_532772 : CollatzResearch.WordTrace tailWord_532772 prefixEnd_532772 81057219335494743940691 := by
  unfold tailWord_532772
  simp only [CollatzResearch.WordTrace]
  refine ⟨9715895612932754529304285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12954527483910339372405713 9715895612932754529304285)
  ·
    refine ⟨3643460854849782948489107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9715895612932754529304285 3643460854849782948489107)
    ·
      refine ⟨5465191282274674422733661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3643460854849782948489107 5465191282274674422733661)
      ·
        refine ⟨2049446730853002908525123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5465191282274674422733661 2049446730853002908525123)
        ·
          refine ⟨3074170096279504362787685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2049446730853002908525123 3074170096279504362787685)
          ·
            refine ⟨576406893052407068022691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3074170096279504362787685 576406893052407068022691)
            ·
              refine ⟨864610339578610602034037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576406893052407068022691 864610339578610602034037)
              ·
                refine ⟨81057219335494743940691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 864610339578610602034037 81057219335494743940691)
                ·
                  rfl

theorem cell20_532772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_532772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532772 prefixEnd_532772 := by exact prefixLift 532772
  have htrace : WordTrace (prefixWord ++ tailWord_532772) baseStart_532772 baseEnd_532772 := by
    simpa [prefixWord, tailWord_532772, baseEnd_532772] using wordTrace_append hprefix tailTrace_532772
  have hstable : (prefixWord ++ tailWord_532772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532772).length < 2 ^ (prefixWord ++ tailWord_532772).sum := by decide
  have hdescent : baseEnd_532772 < baseStart_532772 := by decide
  rcases family_descends (prefixWord ++ tailWord_532772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532782 : List Nat := [4, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_532782 : Nat := 118140960795 + 532782 * 2 ^ 59
def prefixEnd_532782 : Nat := 4983230072969 + 3 ^ 40 * 532782 * 2
def baseEnd_532782 : Nat := 243176222278968641488699

theorem tailTrace_532782 : CollatzResearch.WordTrace tailWord_532782 prefixEnd_532782 243176222278968641488699 := by
  unfold tailWord_532782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2429019494478660095809075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12954770637219520510981733 2429019494478660095809075)
  ·
    refine ⟨3643529241717990143713613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2429019494478660095809075 3643529241717990143713613)
    ·
      refine ⟨1366323465644246303892605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3643529241717990143713613 1366323465644246303892605)
      ·
        refine ⟨512371299616592363959727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1366323465644246303892605 512371299616592363959727)
        ·
          refine ⟨768556949424888545939591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512371299616592363959727 768556949424888545939591)
          ·
            refine ⟨1152835424137332818909387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768556949424888545939591 1152835424137332818909387)
            ·
              refine ⟨1729253136205999228364081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152835424137332818909387 1729253136205999228364081)
              ·
                refine ⟨1296939852154499421273061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1729253136205999228364081 1296939852154499421273061)
                ·
                  refine ⟨243176222278968641488699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1296939852154499421273061 243176222278968641488699)
                  ·
                    rfl

theorem cell20_532782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_532782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532782 prefixEnd_532782 := by exact prefixLift 532782
  have htrace : WordTrace (prefixWord ++ tailWord_532782) baseStart_532782 baseEnd_532782 := by
    simpa [prefixWord, tailWord_532782, baseEnd_532782] using wordTrace_append hprefix tailTrace_532782
  have hstable : (prefixWord ++ tailWord_532782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532782).length < 2 ^ (prefixWord ++ tailWord_532782).sum := by decide
  have hdescent : baseEnd_532782 < baseStart_532782 := by decide
  rcases family_descends (prefixWord ++ tailWord_532782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532807 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 6]
def baseStart_532807 : Nat := 118140960795 + 532807 * 2 ^ 59
def prefixEnd_532807 : Nat := 4983230072969 + 3 ^ 40 * 532807 * 2
def baseEnd_532807 : Nat := 243187632960179665655263

theorem tailTrace_532807 : CollatzResearch.WordTrace tailWord_532807 prefixEnd_532807 243187632960179665655263 := by
  unfold tailWord_532807
  simp only [CollatzResearch.WordTrace]
  refine ⟨19433067780738710036132675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12955378520492473357421783 19433067780738710036132675)
  ·
    refine ⟨29149601671108065054199013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19433067780738710036132675 29149601671108065054199013)
    ·
      refine ⟨5465550313332762197662315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29149601671108065054199013 5465550313332762197662315)
      ·
        refine ⟨8198325469999143296493473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5465550313332762197662315 8198325469999143296493473)
        ·
          refine ⟨6148744102499357472370105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8198325469999143296493473 6148744102499357472370105)
          ·
            refine ⟨4611558076874518104277579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6148744102499357472370105 4611558076874518104277579)
            ·
              refine ⟨6917337115311777156416369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4611558076874518104277579 6917337115311777156416369)
              ·
                refine ⟨5188002836483832867312277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6917337115311777156416369 5188002836483832867312277)
                ·
                  refine ⟨243187632960179665655263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5188002836483832867312277 243187632960179665655263)
                  ·
                    rfl

theorem cell20_532807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_532807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532807 prefixEnd_532807 := by exact prefixLift 532807
  have htrace : WordTrace (prefixWord ++ tailWord_532807) baseStart_532807 baseEnd_532807 := by
    simpa [prefixWord, tailWord_532807, baseEnd_532807] using wordTrace_append hprefix tailTrace_532807
  have hstable : (prefixWord ++ tailWord_532807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532807).length < 2 ^ (prefixWord ++ tailWord_532807).sum := by decide
  have hdescent : baseEnd_532807 < baseStart_532807 := by decide
  rcases family_descends (prefixWord ++ tailWord_532807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532817 : List Nat := [1, 2, 2, 1, 4, 2, 3, 2, 3]
def baseStart_532817 : Nat := 118140960795 + 532817 * 2 ^ 59
def prefixEnd_532817 : Nat := 4983230072969 + 3 ^ 40 * 532817 * 2
def baseEnd_532817 : Nat := 243192197232664075321889

theorem tailTrace_532817 : CollatzResearch.WordTrace tailWord_532817 prefixEnd_532817 243192197232664075321889 := by
  unfold tailWord_532817
  simp only [CollatzResearch.WordTrace]
  refine ⟨19433432510702481743996705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12955621673801654495997803 19433432510702481743996705)
  ·
    refine ⟨14575074383026861307997529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19433432510702481743996705 14575074383026861307997529)
    ·
      refine ⟨10931305787270145980998147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14575074383026861307997529 10931305787270145980998147)
      ·
        refine ⟨16396958680905218971497221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10931305787270145980998147 16396958680905218971497221)
        ·
          refine ⟨3074429752669728557155729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16396958680905218971497221 3074429752669728557155729)
          ·
            refine ⟨2305822314502296417866797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3074429752669728557155729 2305822314502296417866797)
            ·
              refine ⟨864683367938361156700049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2305822314502296417866797 864683367938361156700049)
              ·
                refine ⟨648512525953770867525037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864683367938361156700049 648512525953770867525037)
                ·
                  refine ⟨243192197232664075321889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 648512525953770867525037 243192197232664075321889)
                  ·
                    rfl

theorem cell20_532817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_532817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532817 prefixEnd_532817 := by exact prefixLift 532817
  have htrace : WordTrace (prefixWord ++ tailWord_532817) baseStart_532817 baseEnd_532817 := by
    simpa [prefixWord, tailWord_532817, baseEnd_532817] using wordTrace_append hprefix tailTrace_532817
  have hstable : (prefixWord ++ tailWord_532817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532817).length < 2 ^ (prefixWord ++ tailWord_532817).sum := by decide
  have hdescent : baseEnd_532817 < baseStart_532817 := by decide
  rcases family_descends (prefixWord ++ tailWord_532817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532848 : List Nat := [2, 1, 1, 1, 4, 5, 2, 4]
def baseStart_532848 : Nat := 118140960795 + 532848 * 2 ^ 59
def prefixEnd_532848 : Nat := 4983230072969 + 3 ^ 40 * 532848 * 2
def baseEnd_532848 : Nat := 81068782159121915096143

theorem tailTrace_532848 : CollatzResearch.WordTrace tailWord_532848 prefixEnd_532848 81068782159121915096143 := by
  unfold tailWord_532848
  simp only [CollatzResearch.WordTrace]
  refine ⟨9717281586795087019187599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12956375449060116025583465 9717281586795087019187599)
  ·
    refine ⟨14575922380192630528781399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9717281586795087019187599 14575922380192630528781399)
    ·
      refine ⟨21863883570288945793172099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14575922380192630528781399 21863883570288945793172099)
      ·
        refine ⟨32795825355433418689758149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21863883570288945793172099 32795825355433418689758149)
        ·
          refine ⟨6149217254143766004329653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32795825355433418689758149 6149217254143766004329653)
          ·
            refine ⟨576489117575978062905905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6149217254143766004329653 576489117575978062905905)
            ·
              refine ⟨432366838181983547179429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576489117575978062905905 432366838181983547179429)
              ·
                refine ⟨81068782159121915096143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 432366838181983547179429 81068782159121915096143)
                ·
                  rfl

theorem cell20_532848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_532848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532848 prefixEnd_532848 := by exact prefixLift 532848
  have htrace : WordTrace (prefixWord ++ tailWord_532848) baseStart_532848 baseEnd_532848 := by
    simpa [prefixWord, tailWord_532848, baseEnd_532848] using wordTrace_append hprefix tailTrace_532848
  have hstable : (prefixWord ++ tailWord_532848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532848).length < 2 ^ (prefixWord ++ tailWord_532848).sum := by decide
  have hdescent : baseEnd_532848 < baseStart_532848 := by decide
  rcases family_descends (prefixWord ++ tailWord_532848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532854 : List Nat := [5, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_532854 : Nat := 118140960795 + 532854 * 2 ^ 59
def prefixEnd_532854 : Nat := 4983230072969 + 3 ^ 40 * 532854 * 2
def baseEnd_532854 : Nat := 243209085040856391088405

theorem tailTrace_532854 : CollatzResearch.WordTrace tailWord_532854 prefixEnd_532854 243209085040856391088405 := by
  unfold tailWord_532854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1214673875723027316443351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12956521341045624708729077 1214673875723027316443351)
  ·
    refine ⟨1822010813584540974665027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1214673875723027316443351 1822010813584540974665027)
    ·
      refine ⟨2733016220376811461997541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1822010813584540974665027 2733016220376811461997541)
      ·
        refine ⟨512440541320652149124539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2733016220376811461997541 512440541320652149124539)
        ·
          refine ⟨768660811980978223686809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512440541320652149124539 768660811980978223686809)
          ·
            refine ⟨576495608985733667765107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 768660811980978223686809 576495608985733667765107)
            ·
              refine ⟨864743413478600501647661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576495608985733667765107 864743413478600501647661)
              ·
                refine ⟨324278780054475188117873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 864743413478600501647661 324278780054475188117873)
                ·
                  refine ⟨243209085040856391088405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324278780054475188117873 243209085040856391088405)
                  ·
                    rfl

theorem cell20_532854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_532854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532854 prefixEnd_532854 := by exact prefixLift 532854
  have htrace : WordTrace (prefixWord ++ tailWord_532854) baseStart_532854 baseEnd_532854 := by
    simpa [prefixWord, tailWord_532854, baseEnd_532854] using wordTrace_append hprefix tailTrace_532854
  have hstable : (prefixWord ++ tailWord_532854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532854).length < 2 ^ (prefixWord ++ tailWord_532854).sum := by decide
  have hdescent : baseEnd_532854 < baseStart_532854 := by decide
  rcases family_descends (prefixWord ++ tailWord_532854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532876 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 5]
def baseStart_532876 : Nat := 118140960795 + 532876 * 2 ^ 59
def prefixEnd_532876 : Nat := 4983230072969 + 3 ^ 40 * 532876 * 2
def baseEnd_532876 : Nat := 243219126440322092354981

theorem tailTrace_532876 : CollatzResearch.WordTrace tailWord_532876 prefixEnd_532876 243219126440322092354981 := by
  unfold tailWord_532876
  simp only [CollatzResearch.WordTrace]
  refine ⟨9717792208744367410197241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12957056278325823213596321 9717792208744367410197241)
  ·
    refine ⟨7288344156558275557647931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9717792208744367410197241 7288344156558275557647931)
    ·
      refine ⟨10932516234837413336471897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7288344156558275557647931 10932516234837413336471897)
      ·
        refine ⟨8199387176128060002353923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10932516234837413336471897 8199387176128060002353923)
        ·
          refine ⟨12299080764192090003530885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8199387176128060002353923 12299080764192090003530885)
          ·
            refine ⟨2306077643286016875662041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12299080764192090003530885 2306077643286016875662041)
            ·
              refine ⟨1729558232464512656746531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2306077643286016875662041 1729558232464512656746531)
              ·
                refine ⟨2594337348696768985119797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1729558232464512656746531 2594337348696768985119797)
                ·
                  refine ⟨243219126440322092354981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2594337348696768985119797 243219126440322092354981)
                  ·
                    rfl

theorem cell20_532876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_532876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532876 prefixEnd_532876 := by exact prefixLift 532876
  have htrace : WordTrace (prefixWord ++ tailWord_532876) baseStart_532876 baseEnd_532876 := by
    simpa [prefixWord, tailWord_532876, baseEnd_532876] using wordTrace_append hprefix tailTrace_532876
  have hstable : (prefixWord ++ tailWord_532876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532876).length < 2 ^ (prefixWord ++ tailWord_532876).sum := by decide
  have hdescent : baseEnd_532876 < baseStart_532876 := by decide
  rcases family_descends (prefixWord ++ tailWord_532876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532959 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 6]
def baseStart_532959 : Nat := 118140960795 + 532959 * 2 ^ 59
def prefixEnd_532959 : Nat := 4983230072969 + 3 ^ 40 * 532959 * 2
def baseEnd_532959 : Nat := 243257009901942692587975

theorem tailTrace_532959 : CollatzResearch.WordTrace tailWord_532959 prefixEnd_532959 243257009901942692587975 := by
  unfold tailWord_532959
  simp only [CollatzResearch.WordTrace]
  refine ⟨19438611676188039995665931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12959074450792026663777287 19438611676188039995665931)
  ·
    refine ⟨29157917514282059993498897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19438611676188039995665931 29157917514282059993498897)
    ·
      refine ⟨21868438135711544995124173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29157917514282059993498897 21868438135711544995124173)
      ·
        refine ⟨8200664300891829373171565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21868438135711544995124173 8200664300891829373171565)
        ·
          refine ⟨3075249112834436014939337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8200664300891829373171565 3075249112834436014939337)
          ·
            refine ⟨2306436834625827011204503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3075249112834436014939337 2306436834625827011204503)
            ·
              refine ⟨3459655251938740516806755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2306436834625827011204503 3459655251938740516806755)
              ·
                refine ⟨5189482877908110775210133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3459655251938740516806755 5189482877908110775210133)
                ·
                  refine ⟨243257009901942692587975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5189482877908110775210133 243257009901942692587975)
                  ·
                    rfl

theorem cell20_532959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_532959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532959 prefixEnd_532959 := by exact prefixLift 532959
  have htrace : WordTrace (prefixWord ++ tailWord_532959) baseStart_532959 baseEnd_532959 := by
    simpa [prefixWord, tailWord_532959, baseEnd_532959] using wordTrace_append hprefix tailTrace_532959
  have hstable : (prefixWord ++ tailWord_532959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532959).length < 2 ^ (prefixWord ++ tailWord_532959).sum := by decide
  have hdescent : baseEnd_532959 < baseStart_532959 := by decide
  rcases family_descends (prefixWord ++ tailWord_532959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532993 : List Nat := [1, 2, 4, 1, 3, 1, 2, 4, 2]
def baseStart_532993 : Nat := 118140960795 + 532993 * 2 ^ 59
def prefixEnd_532993 : Nat := 4983230072969 + 3 ^ 40 * 532993 * 2
def baseEnd_532993 : Nat := 243272528428389685454503

theorem tailTrace_532993 : CollatzResearch.WordTrace tailWord_532993 prefixEnd_532993 243272528428389685454503 := by
  unfold tailWord_532993
  simp only [CollatzResearch.WordTrace]
  refine ⟨19439851758064863802403633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12959901172043242534935755 19439851758064863802403633)
  ·
    refine ⟨14579888818548647851802725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19439851758064863802403633 14579888818548647851802725)
    ·
      refine ⟨2733729153477871472213011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14579888818548647851802725 2733729153477871472213011)
      ·
        refine ⟨4100593730216807208319517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2733729153477871472213011 4100593730216807208319517)
        ·
          refine ⟨1537722648831302703119819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4100593730216807208319517 1537722648831302703119819)
          ·
            refine ⟨2306583973246954054679729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1537722648831302703119819 2306583973246954054679729)
            ·
              refine ⟨1729937979935215541009797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2306583973246954054679729 1729937979935215541009797)
              ·
                refine ⟨324363371237852913939337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1729937979935215541009797 324363371237852913939337)
                ·
                  refine ⟨243272528428389685454503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324363371237852913939337 243272528428389685454503)
                  ·
                    rfl

theorem cell20_532993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 2].length) (baseStart_532993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532993 prefixEnd_532993 := by exact prefixLift 532993
  have htrace : WordTrace (prefixWord ++ tailWord_532993) baseStart_532993 baseEnd_532993 := by
    simpa [prefixWord, tailWord_532993, baseEnd_532993] using wordTrace_append hprefix tailTrace_532993
  have hstable : (prefixWord ++ tailWord_532993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532993).length < 2 ^ (prefixWord ++ tailWord_532993).sum := by decide
  have hdescent : baseEnd_532993 < baseStart_532993 := by decide
  rcases family_descends (prefixWord ++ tailWord_532993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532997 : List Nat := [1, 3, 1, 1, 2, 2, 3, 3, 4]
def baseStart_532997 : Nat := 118140960795 + 532997 * 2 ^ 59
def prefixEnd_532997 : Nat := 4983230072969 + 3 ^ 40 * 532997 * 2
def baseEnd_532997 : Nat := 243274354137383449321153

theorem tailTrace_532997 : CollatzResearch.WordTrace tailWord_532997 prefixEnd_532997 243274354137383449321153 := by
  unfold tailWord_532997
  simp only [CollatzResearch.WordTrace]
  refine ⟨19439997650050372485549245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12959998433366914990366163 19439997650050372485549245)
  ·
    refine ⟨7289999118768889682080967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19439997650050372485549245 7289999118768889682080967)
    ·
      refine ⟨10934998678153334523121451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7289999118768889682080967 10934998678153334523121451)
      ·
        refine ⟨16402498017230001784682177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10934998678153334523121451 16402498017230001784682177)
        ·
          refine ⟨12301873512922501338511633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16402498017230001784682177 12301873512922501338511633)
          ·
            refine ⟨9226405134691876003883725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12301873512922501338511633 9226405134691876003883725)
            ·
              refine ⟨3459901925509453501456397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9226405134691876003883725 3459901925509453501456397)
              ·
                refine ⟨1297463222066045063046149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3459901925509453501456397 1297463222066045063046149)
                ·
                  refine ⟨243274354137383449321153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1297463222066045063046149 243274354137383449321153)
                  ·
                    rfl

theorem cell20_532997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_532997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_532997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_532997 prefixEnd_532997 := by exact prefixLift 532997
  have htrace : WordTrace (prefixWord ++ tailWord_532997) baseStart_532997 baseEnd_532997 := by
    simpa [prefixWord, tailWord_532997, baseEnd_532997] using wordTrace_append hprefix tailTrace_532997
  have hstable : (prefixWord ++ tailWord_532997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532997).length < 2 ^ (prefixWord ++ tailWord_532997).sum := by decide
  have hdescent : baseEnd_532997 < baseStart_532997 := by decide
  rcases family_descends (prefixWord ++ tailWord_532997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533021 : List Nat := [1, 4, 2, 2, 1, 3, 1, 6]
def baseStart_533021 : Nat := 118140960795 + 533021 * 2 ^ 59
def prefixEnd_533021 : Nat := 4983230072969 + 3 ^ 40 * 533021 * 2
def baseEnd_533021 : Nat := 81095102797115344173685

theorem tailTrace_533021 : CollatzResearch.WordTrace tailWord_533021 prefixEnd_533021 81095102797115344173685 := by
  unfold tailWord_533021
  simp only [CollatzResearch.WordTrace]
  refine ⟨19440873001963424584422917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12960582001308949722948611 19440873001963424584422917)
  ·
    refine ⟨3645163687868142109579297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19440873001963424584422917 3645163687868142109579297)
    ·
      refine ⟨2733872765901106582184473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3645163687868142109579297 2733872765901106582184473)
      ·
        refine ⟨2050404574425829936638355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2733872765901106582184473 2050404574425829936638355)
        ·
          refine ⟨3075606861638744904957533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2050404574425829936638355 3075606861638744904957533)
          ·
            refine ⟨1153352573114529339359075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3075606861638744904957533 1153352573114529339359075)
            ·
              refine ⟨1730028859671794009038613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1153352573114529339359075 1730028859671794009038613)
              ·
                refine ⟨81095102797115344173685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1730028859671794009038613 81095102797115344173685)
                ·
                  rfl

theorem cell20_533021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 6].length) (baseStart_533021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533021 prefixEnd_533021 := by exact prefixLift 533021
  have htrace : WordTrace (prefixWord ++ tailWord_533021) baseStart_533021 baseEnd_533021 := by
    simpa [prefixWord, tailWord_533021, baseEnd_533021] using wordTrace_append hprefix tailTrace_533021
  have hstable : (prefixWord ++ tailWord_533021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533021).length < 2 ^ (prefixWord ++ tailWord_533021).sum := by decide
  have hdescent : baseEnd_533021 < baseStart_533021 := by decide
  rcases family_descends (prefixWord ++ tailWord_533021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533038 : List Nat := [4, 1, 3, 1, 3, 2, 6]
def baseStart_533038 : Nat := 118140960795 + 533038 * 2 ^ 59
def prefixEnd_533038 : Nat := 4983230072969 + 3 ^ 40 * 533038 * 2
def baseEnd_533038 : Nat := 27032563072729947661591

theorem tailTrace_533038 : CollatzResearch.WordTrace tailWord_533038 prefixEnd_533038 27032563072729947661591 := by
  unfold tailWord_533038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2430186630362729560973971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12960995361934557658527845 2430186630362729560973971)
  ·
    refine ⟨3645279945544094341460957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2430186630362729560973971 3645279945544094341460957)
    ·
      refine ⟨1366979979579035378047859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3645279945544094341460957 1366979979579035378047859)
      ·
        refine ⟨2050469969368553067071789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1366979979579035378047859 2050469969368553067071789)
        ·
          refine ⟨768926238513207400151921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2050469969368553067071789 768926238513207400151921)
          ·
            refine ⟨576694678884905550113941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 768926238513207400151921 576694678884905550113941)
            ·
              refine ⟨27032563072729947661591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 576694678884905550113941 27032563072729947661591)
              ·
                rfl

theorem cell20_533038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 6].length) (baseStart_533038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533038 prefixEnd_533038 := by exact prefixLift 533038
  have htrace : WordTrace (prefixWord ++ tailWord_533038) baseStart_533038 baseEnd_533038 := by
    simpa [prefixWord, tailWord_533038, baseEnd_533038] using wordTrace_append hprefix tailTrace_533038
  have hstable : (prefixWord ++ tailWord_533038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533038).length < 2 ^ (prefixWord ++ tailWord_533038).sum := by decide
  have hdescent : baseEnd_533038 < baseStart_533038 := by decide
  rcases family_descends (prefixWord ++ tailWord_533038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533042 : List Nat := [3, 2, 1, 1, 2, 1, 10]
def baseStart_533042 : Nat := 118140960795 + 533042 * 2 ^ 59
def prefixEnd_533042 : Nat := 4983230072969 + 3 ^ 40 * 533042 * 2
def baseEnd_533042 : Nat := 27032765929284810313441

theorem tailTrace_533042 : CollatzResearch.WordTrace tailWord_533042 prefixEnd_533042 27032765929284810313441 := by
  unfold tailWord_533042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4860409733721836292734345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12961092623258230113958253 4860409733721836292734345)
  ·
    refine ⟨3645307300291377219550759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4860409733721836292734345 3645307300291377219550759)
    ·
      refine ⟨5467960950437065829326139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3645307300291377219550759 5467960950437065829326139)
      ·
        refine ⟨8201941425655598743989209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5467960950437065829326139 8201941425655598743989209)
        ·
          refine ⟨6151456069241699057991907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8201941425655598743989209 6151456069241699057991907)
          ·
            refine ⟨9227184103862548586987861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6151456069241699057991907 9227184103862548586987861)
            ·
              refine ⟨27032765929284810313441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9227184103862548586987861 27032765929284810313441)
              ·
                rfl

theorem cell20_533042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 10].length) (baseStart_533042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533042 prefixEnd_533042 := by exact prefixLift 533042
  have htrace : WordTrace (prefixWord ++ tailWord_533042) baseStart_533042 baseEnd_533042 := by
    simpa [prefixWord, tailWord_533042, baseEnd_533042] using wordTrace_append hprefix tailTrace_533042
  have hstable : (prefixWord ++ tailWord_533042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533042).length < 2 ^ (prefixWord ++ tailWord_533042).sum := by decide
  have hdescent : baseEnd_533042 < baseStart_533042 := by decide
  rcases family_descends (prefixWord ++ tailWord_533042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533044 : List Nat := [2, 5, 1, 3, 1, 1, 3, 2, 2]
def baseStart_533044 : Nat := 118140960795 + 533044 * 2 ^ 59
def prefixEnd_533044 : Nat := 4983230072969 + 3 ^ 40 * 533044 * 2
def baseEnd_533044 : Nat := 243295806218060174754295

theorem tailTrace_533044 : CollatzResearch.WordTrace tailWord_533044 prefixEnd_533044 243295806218060174754295 := by
  unfold tailWord_533044
  simp only [CollatzResearch.WordTrace]
  refine ⟨9720855940440049756255093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12961141253920066341673457 9720855940440049756255093)
  ·
    refine ⟨911330244416254664648915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9720855940440049756255093 911330244416254664648915)
    ·
      refine ⟨1366995366624381996973373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 911330244416254664648915 1366995366624381996973373)
      ·
        refine ⟨512623262484143248865015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1366995366624381996973373 512623262484143248865015)
        ·
          refine ⟨768934893726214873297523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512623262484143248865015 768934893726214873297523)
          ·
            refine ⟨1153402340589322309946285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768934893726214873297523 1153402340589322309946285)
            ·
              refine ⟨432525877720995866229857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1153402340589322309946285 432525877720995866229857)
              ·
                refine ⟨324394408290746899672393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432525877720995866229857 324394408290746899672393)
                ·
                  refine ⟨243295806218060174754295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324394408290746899672393 243295806218060174754295)
                  ·
                    rfl

theorem cell20_533044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_533044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533044 prefixEnd_533044 := by exact prefixLift 533044
  have htrace : WordTrace (prefixWord ++ tailWord_533044) baseStart_533044 baseEnd_533044 := by
    simpa [prefixWord, tailWord_533044, baseEnd_533044] using wordTrace_append hprefix tailTrace_533044
  have hstable : (prefixWord ++ tailWord_533044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533044).length < 2 ^ (prefixWord ++ tailWord_533044).sum := by decide
  have hdescent : baseEnd_533044 < baseStart_533044 := by decide
  rcases family_descends (prefixWord ++ tailWord_533044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533052 : List Nat := [2, 2, 2, 2, 3, 1, 3, 1, 4]
def baseStart_533052 : Nat := 118140960795 + 533052 * 2 ^ 59
def prefixEnd_533052 : Nat := 4983230072969 + 3 ^ 40 * 533052 * 2
def baseEnd_533052 : Nat := 243299457636047702487595

theorem tailTrace_533052 : CollatzResearch.WordTrace tailWord_533052 prefixEnd_533052 243299457636047702487595 := by
  unfold tailWord_533052
  simp only [CollatzResearch.WordTrace]
  refine ⟨9721001832425558439400705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12961335776567411252534273 9721001832425558439400705)
  ·
    refine ⟨7290751374319168829550529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9721001832425558439400705 7290751374319168829550529)
    ·
      refine ⟨5468063530739376622162897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7290751374319168829550529 5468063530739376622162897)
      ·
        refine ⟨4101047648054532466622173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5468063530739376622162897 4101047648054532466622173)
        ·
          refine ⟨1537892868020449674983315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4101047648054532466622173 1537892868020449674983315)
          ·
            refine ⟨2306839302030674512474973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1537892868020449674983315 2306839302030674512474973)
            ·
              refine ⟨865064738261502942178115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2306839302030674512474973 865064738261502942178115)
              ·
                refine ⟨1297597107392254413267173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865064738261502942178115 1297597107392254413267173)
                ·
                  refine ⟨243299457636047702487595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1297597107392254413267173 243299457636047702487595)
                  ·
                    rfl

theorem cell20_533052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_533052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533052 prefixEnd_533052 := by exact prefixLift 533052
  have htrace : WordTrace (prefixWord ++ tailWord_533052) baseStart_533052 baseEnd_533052 := by
    simpa [prefixWord, tailWord_533052, baseEnd_533052] using wordTrace_append hprefix tailTrace_533052
  have hstable : (prefixWord ++ tailWord_533052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533052).length < 2 ^ (prefixWord ++ tailWord_533052).sum := by decide
  have hdescent : baseEnd_533052 < baseStart_533052 := by decide
  rcases family_descends (prefixWord ++ tailWord_533052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533080 : List Nat := [2, 1, 2, 2, 1, 2, 4, 6]
def baseStart_533080 : Nat := 118140960795 + 533080 * 2 ^ 59
def prefixEnd_533080 : Nat := 4983230072969 + 3 ^ 40 * 533080 * 2
def baseEnd_533080 : Nat := 81104079199668016518049

theorem tailTrace_533080 : CollatzResearch.WordTrace tailWord_533080 prefixEnd_533080 81104079199668016518049 := by
  unfold tailWord_533080
  simp only [CollatzResearch.WordTrace]
  refine ⟨9721512454374838830410347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12962016605833118440547129 9721512454374838830410347)
  ·
    refine ⟨14582268681562258245615521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9721512454374838830410347 14582268681562258245615521)
    ·
      refine ⟨10936701511171693684211641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14582268681562258245615521 10936701511171693684211641)
      ·
        refine ⟨8202526133378770263158731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10936701511171693684211641 8202526133378770263158731)
        ·
          refine ⟨12303789200068155394738097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8202526133378770263158731 12303789200068155394738097)
          ·
            refine ⟨9227841900051116546053573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12303789200068155394738097 9227841900051116546053573)
            ·
              refine ⟨1730220356259584352385045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9227841900051116546053573 1730220356259584352385045)
              ·
                refine ⟨81104079199668016518049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1730220356259584352385045 81104079199668016518049)
                ·
                  rfl

theorem cell20_533080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_533080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533080 prefixEnd_533080 := by exact prefixLift 533080
  have htrace : WordTrace (prefixWord ++ tailWord_533080) baseStart_533080 baseEnd_533080 := by
    simpa [prefixWord, tailWord_533080, baseEnd_533080] using wordTrace_append hprefix tailTrace_533080
  have hstable : (prefixWord ++ tailWord_533080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533080).length < 2 ^ (prefixWord ++ tailWord_533080).sum := by decide
  have hdescent : baseEnd_533080 < baseStart_533080 := by decide
  rcases family_descends (prefixWord ++ tailWord_533080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533087 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 7]
def baseStart_533087 : Nat := 118140960795 + 533087 * 2 ^ 59
def prefixEnd_533087 : Nat := 4983230072969 + 3 ^ 40 * 533087 * 2
def baseEnd_533087 : Nat := 243315432589743136320785

theorem tailTrace_533087 : CollatzResearch.WordTrace tailWord_533087 prefixEnd_533087 243315432589743136320785 := by
  unfold tailWord_533087
  simp only [CollatzResearch.WordTrace]
  refine ⟨19443280219724317856325515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12962186813149545237550343 19443280219724317856325515)
  ·
    refine ⟨29164920329586476784488273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19443280219724317856325515 29164920329586476784488273)
    ·
      refine ⟨21873690247189857588366205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29164920329586476784488273 21873690247189857588366205)
      ·
        refine ⟨8202633842696196595637327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21873690247189857588366205 8202633842696196595637327)
        ·
          refine ⟨12303950764044294893455991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8202633842696196595637327 12303950764044294893455991)
          ·
            refine ⟨18455926146066442340183987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12303950764044294893455991 18455926146066442340183987)
            ·
              refine ⟨27683889219099663510275981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18455926146066442340183987 27683889219099663510275981)
              ·
                refine ⟨10381458457162373816353493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27683889219099663510275981 10381458457162373816353493)
                ·
                  refine ⟨243315432589743136320785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10381458457162373816353493 243315432589743136320785)
                  ·
                    rfl

theorem cell20_533087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_533087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533087 prefixEnd_533087 := by exact prefixLift 533087
  have htrace : WordTrace (prefixWord ++ tailWord_533087) baseStart_533087 baseEnd_533087 := by
    simpa [prefixWord, tailWord_533087, baseEnd_533087] using wordTrace_append hprefix tailTrace_533087
  have hstable : (prefixWord ++ tailWord_533087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533087).length < 2 ^ (prefixWord ++ tailWord_533087).sum := by decide
  have hdescent : baseEnd_533087 < baseStart_533087 := by decide
  rcases family_descends (prefixWord ++ tailWord_533087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533156 : List Nat := [2, 3, 1, 2, 2, 1, 9]
def baseStart_533156 : Nat := 118140960795 + 533156 * 2 ^ 59
def prefixEnd_533156 : Nat := 4983230072969 + 3 ^ 40 * 533156 * 2
def baseEnd_533156 : Nat := 27038547341098395891167

theorem tailTrace_533156 : CollatzResearch.WordTrace tailWord_533156 prefixEnd_533156 27038547341098395891167 := by
  unfold tailWord_533156
  simp only [CollatzResearch.WordTrace]
  refine ⟨9722898428237171320293661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12963864570982895093724881 9722898428237171320293661)
  ·
    refine ⟨3646086910588939245110123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9722898428237171320293661 3646086910588939245110123)
    ·
      refine ⟨5469130365883408867665185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3646086910588939245110123 5469130365883408867665185)
      ·
        refine ⟨4101847774412556650748889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5469130365883408867665185 4101847774412556650748889)
        ·
          refine ⟨3076385830809417488061667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4101847774412556650748889 3076385830809417488061667)
          ·
            refine ⟨4614578746214126232092501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3076385830809417488061667 4614578746214126232092501)
            ·
              refine ⟨27038547341098395891167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4614578746214126232092501 27038547341098395891167)
              ·
                rfl

theorem cell20_533156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 9].length) (baseStart_533156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533156 prefixEnd_533156 := by exact prefixLift 533156
  have htrace : WordTrace (prefixWord ++ tailWord_533156) baseStart_533156 baseEnd_533156 := by
    simpa [prefixWord, tailWord_533156, baseEnd_533156] using wordTrace_append hprefix tailTrace_533156
  have hstable : (prefixWord ++ tailWord_533156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533156).length < 2 ^ (prefixWord ++ tailWord_533156).sum := by decide
  have hdescent : baseEnd_533156 < baseStart_533156 := by decide
  rcases family_descends (prefixWord ++ tailWord_533156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533162 : List Nat := [3, 1, 5, 2, 1, 1, 2, 1, 4]
def baseStart_533162 : Nat := 118140960795 + 533162 * 2 ^ 59
def prefixEnd_533162 : Nat := 4983230072969 + 3 ^ 40 * 533162 * 2
def baseEnd_533162 : Nat := 243349664633376208820479

theorem tailTrace_533162 : CollatzResearch.WordTrace tailWord_533162 prefixEnd_533162 243349664633376208820479 := by
  unfold tailWord_533162
  simp only [CollatzResearch.WordTrace]
  refine ⟨4861503923613151416326435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12964010462968403776870493 4861503923613151416326435)
  ·
    refine ⟨7292255885419727124489653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4861503923613151416326435 7292255885419727124489653)
    ·
      refine ⟨683648989258099417920905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7292255885419727124489653 683648989258099417920905)
      ·
        refine ⟨512736741943574563440679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683648989258099417920905 512736741943574563440679)
        ·
          refine ⟨769105112915361845161019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512736741943574563440679 769105112915361845161019)
          ·
            refine ⟨1153657669373042767741529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769105112915361845161019 1153657669373042767741529)
            ·
              refine ⟨865243252029782075806147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1153657669373042767741529 865243252029782075806147)
              ·
                refine ⟨1297864878044673113709221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865243252029782075806147 1297864878044673113709221)
                ·
                  refine ⟨243349664633376208820479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1297864878044673113709221 243349664633376208820479)
                  ·
                    rfl

theorem cell20_533162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_533162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533162 prefixEnd_533162 := by exact prefixLift 533162
  have htrace : WordTrace (prefixWord ++ tailWord_533162) baseStart_533162 baseEnd_533162 := by
    simpa [prefixWord, tailWord_533162, baseEnd_533162] using wordTrace_append hprefix tailTrace_533162
  have hstable : (prefixWord ++ tailWord_533162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533162).length < 2 ^ (prefixWord ++ tailWord_533162).sum := by decide
  have hdescent : baseEnd_533162 < baseStart_533162 := by decide
  rcases family_descends (prefixWord ++ tailWord_533162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533201 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 7]
def baseStart_533201 : Nat := 118140960795 + 533201 * 2 ^ 59
def prefixEnd_533201 : Nat := 4983230072969 + 3 ^ 40 * 533201 * 2
def baseEnd_533201 : Nat := 243367465296065406520319

theorem tailTrace_533201 : CollatzResearch.WordTrace tailWord_533201 prefixEnd_533201 243367465296065406520319 := by
  unfold tailWord_533201
  simp only [CollatzResearch.WordTrace]
  refine ⟨19447438141311315325975457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12964958760874210217316971 19447438141311315325975457)
  ·
    refine ⟨14585578605983486494481593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19447438141311315325975457 14585578605983486494481593)
    ·
      refine ⟨10939183954487614870861195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14585578605983486494481593 10939183954487614870861195)
      ·
        refine ⟨16408775931731422306291793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10939183954487614870861195 16408775931731422306291793)
        ·
          refine ⟨12306581948798566729718845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16408775931731422306291793 12306581948798566729718845)
          ·
            refine ⟨4614968230799462523644567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12306581948798566729718845 4614968230799462523644567)
            ·
              refine ⟨6922452346199193785466851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4614968230799462523644567 6922452346199193785466851)
              ·
                refine ⟨10383678519298790678200277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6922452346199193785466851 10383678519298790678200277)
                ·
                  refine ⟨243367465296065406520319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10383678519298790678200277 243367465296065406520319)
                  ·
                    rfl

theorem cell20_533201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_533201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533201 prefixEnd_533201 := by exact prefixLift 533201
  have htrace : WordTrace (prefixWord ++ tailWord_533201) baseStart_533201 baseEnd_533201 := by
    simpa [prefixWord, tailWord_533201, baseEnd_533201] using wordTrace_append hprefix tailTrace_533201
  have hstable : (prefixWord ++ tailWord_533201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533201).length < 2 ^ (prefixWord ++ tailWord_533201).sum := by decide
  have hdescent : baseEnd_533201 < baseStart_533201 := by decide
  rcases family_descends (prefixWord ++ tailWord_533201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533225 : List Nat := [1, 2, 1, 1, 1, 2, 7, 1, 4]
def baseStart_533225 : Nat := 118140960795 + 533225 * 2 ^ 59
def prefixEnd_533225 : Nat := 4983230072969 + 3 ^ 40 * 533225 * 2
def baseEnd_533225 : Nat := 243378419550027989720221

theorem tailTrace_533225 : CollatzResearch.WordTrace tailWord_533225 prefixEnd_533225 243378419550027989720221 := by
  unfold tailWord_533225
  simp only [CollatzResearch.WordTrace]
  refine ⟨19448313493224367424849129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12965542328816244949899419 19448313493224367424849129)
  ·
    refine ⟨14586235119918275568636847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19448313493224367424849129 14586235119918275568636847)
    ·
      refine ⟨21879352679877413352955271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14586235119918275568636847 21879352679877413352955271)
      ·
        refine ⟨32819029019816120029432907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21879352679877413352955271 32819029019816120029432907)
        ·
          refine ⟨49228543529724180044149361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32819029019816120029432907 49228543529724180044149361)
          ·
            refine ⟨36921407647293135033112021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49228543529724180044149361 36921407647293135033112021)
            ·
              refine ⟨865345491733432852338563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 36921407647293135033112021 865345491733432852338563)
              ·
                refine ⟨1298018237600149278507845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865345491733432852338563 1298018237600149278507845)
                ·
                  refine ⟨243378419550027989720221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1298018237600149278507845 243378419550027989720221)
                  ·
                    rfl

theorem cell20_533225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_533225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533225 prefixEnd_533225 := by exact prefixLift 533225
  have htrace : WordTrace (prefixWord ++ tailWord_533225) baseStart_533225 baseEnd_533225 := by
    simpa [prefixWord, tailWord_533225, baseEnd_533225] using wordTrace_append hprefix tailTrace_533225
  have hstable : (prefixWord ++ tailWord_533225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533225).length < 2 ^ (prefixWord ++ tailWord_533225).sum := by decide
  have hdescent : baseEnd_533225 < baseStart_533225 := by decide
  rcases family_descends (prefixWord ++ tailWord_533225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533232 : List Nat := [2, 1, 1, 1, 3, 1, 6, 5]
def baseStart_533232 : Nat := 118140960795 + 533232 * 2 ^ 59
def prefixEnd_533232 : Nat := 4983230072969 + 3 ^ 40 * 533232 * 2
def baseEnd_533232 : Nat := 81127204846922358828953

theorem tailTrace_533232 : CollatzResearch.WordTrace tailWord_533232 prefixEnd_533232 81127204846922358828953 := by
  unfold tailWord_533232
  simp only [CollatzResearch.WordTrace]
  refine ⟨9724284402099503810176975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12965712536132671746902633 9724284402099503810176975)
  ·
    refine ⟨14586426603149255715265463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9724284402099503810176975 14586426603149255715265463)
    ·
      refine ⟨21879639904723883572898195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14586426603149255715265463 21879639904723883572898195)
      ·
        refine ⟨32819459857085825359347293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21879639904723883572898195 32819459857085825359347293)
        ·
          refine ⟨12307297446407184509755235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32819459857085825359347293 12307297446407184509755235)
          ·
            refine ⟨18460946169610776764632853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12307297446407184509755235 18460946169610776764632853)
            ·
              refine ⟨865356851700505160842165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18460946169610776764632853 865356851700505160842165)
              ·
                refine ⟨81127204846922358828953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 865356851700505160842165 81127204846922358828953)
                ·
                  rfl

theorem cell20_533232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_533232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533232 prefixEnd_533232 := by exact prefixLift 533232
  have htrace : WordTrace (prefixWord ++ tailWord_533232) baseStart_533232 baseEnd_533232 := by
    simpa [prefixWord, tailWord_533232, baseEnd_533232] using wordTrace_append hprefix tailTrace_533232
  have hstable : (prefixWord ++ tailWord_533232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533232).length < 2 ^ (prefixWord ++ tailWord_533232).sum := by decide
  have hdescent : baseEnd_533232 < baseStart_533232 := by decide
  rcases family_descends (prefixWord ++ tailWord_533232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533266 : List Nat := [3, 2, 4, 1, 3, 7]
def baseStart_533266 : Nat := 118140960795 + 533266 * 2 ^ 59
def prefixEnd_533266 : Nat := 4983230072969 + 3 ^ 40 * 533266 * 2
def baseEnd_533266 : Nat := 9014708632119039605681

theorem tailTrace_533266 : CollatzResearch.WordTrace tailWord_533266 prefixEnd_533266 9014708632119039605681 := by
  unfold tailWord_533266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4862452221518957856772913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12966539257383887618061101 4862452221518957856772913)
  ·
    refine ⟨3646839166139218392579685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4862452221518957856772913 3646839166139218392579685)
    ·
      refine ⟨683782343651103448608691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3646839166139218392579685 683782343651103448608691)
      ·
        refine ⟨1025673515476655172913037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683782343651103448608691 1025673515476655172913037)
        ·
          refine ⟨384627568303745689842389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1025673515476655172913037 384627568303745689842389)
          ·
            refine ⟨9014708632119039605681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 384627568303745689842389 9014708632119039605681)
            ·
              rfl

theorem cell20_533266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 7].length) (baseStart_533266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533266 prefixEnd_533266 := by exact prefixLift 533266
  have htrace : WordTrace (prefixWord ++ tailWord_533266) baseStart_533266 baseEnd_533266 := by
    simpa [prefixWord, tailWord_533266, baseEnd_533266] using wordTrace_append hprefix tailTrace_533266
  have hstable : (prefixWord ++ tailWord_533266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533266).length < 2 ^ (prefixWord ++ tailWord_533266).sum := by decide
  have hdescent : baseEnd_533266 < baseStart_533266 := by decide
  rcases family_descends (prefixWord ++ tailWord_533266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533276 : List Nat := [2, 2, 3, 1, 1, 5, 2, 2, 2]
def baseStart_533276 : Nat := 118140960795 + 533276 * 2 ^ 59
def prefixEnd_533276 : Nat := 4983230072969 + 3 ^ 40 * 533276 * 2
def baseEnd_533276 : Nat := 243401697339698479020013

theorem tailTrace_533276 : CollatzResearch.WordTrace tailWord_533276 prefixEnd_533276 243401697339698479020013 := by
  unfold tailWord_533276
  simp only [CollatzResearch.WordTrace]
  refine ⟨9725086808019801567477841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12966782410693068756637121 9725086808019801567477841)
  ·
    refine ⟨7293815106014851175608381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9725086808019801567477841 7293815106014851175608381)
    ·
      refine ⟨2735180664755569190853143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7293815106014851175608381 2735180664755569190853143)
      ·
        refine ⟨4102770997133353786279715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2735180664755569190853143 4102770997133353786279715)
        ·
          refine ⟨6154156495700030679419573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4102770997133353786279715 6154156495700030679419573)
          ·
            refine ⟨576952171471877876195585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6154156495700030679419573 576952171471877876195585)
            ·
              refine ⟨432714128603908407146689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576952171471877876195585 432714128603908407146689)
              ·
                refine ⟨324535596452931305360017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432714128603908407146689 324535596452931305360017)
                ·
                  refine ⟨243401697339698479020013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324535596452931305360017 243401697339698479020013)
                  ·
                    rfl

theorem cell20_533276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_533276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533276 prefixEnd_533276 := by exact prefixLift 533276
  have htrace : WordTrace (prefixWord ++ tailWord_533276) baseStart_533276 baseEnd_533276 := by
    simpa [prefixWord, tailWord_533276, baseEnd_533276] using wordTrace_append hprefix tailTrace_533276
  have hstable : (prefixWord ++ tailWord_533276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533276).length < 2 ^ (prefixWord ++ tailWord_533276).sum := by decide
  have hdescent : baseEnd_533276 < baseStart_533276 := by decide
  rcases family_descends (prefixWord ++ tailWord_533276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533301 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 6]
def baseStart_533301 : Nat := 118140960795 + 533301 * 2 ^ 59
def prefixEnd_533301 : Nat := 4983230072969 + 3 ^ 40 * 533301 * 2
def baseEnd_533301 : Nat := 243413108020909503186577

theorem tailTrace_533301 : CollatzResearch.WordTrace tailWord_533301 prefixEnd_533301 243413108020909503186577 := by
  unfold tailWord_533301
  simp only [CollatzResearch.WordTrace]
  refine ⟨19451085440949032404615757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12967390293966021603077171 19451085440949032404615757)
  ·
    refine ⟨7294157040355887151730909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19451085440949032404615757 7294157040355887151730909)
    ·
      refine ⟨2735308890133457681899091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7294157040355887151730909 2735308890133457681899091)
      ·
        refine ⟨4102963335200186522848637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2735308890133457681899091 4102963335200186522848637)
        ·
          refine ⟨1538611250700069946068239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4102963335200186522848637 1538611250700069946068239)
          ·
            refine ⟨2307916876050104919102359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538611250700069946068239 2307916876050104919102359)
            ·
              refine ⟨3461875314075157378653539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2307916876050104919102359 3461875314075157378653539)
              ·
                refine ⟨5192812971112736067980309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3461875314075157378653539 5192812971112736067980309)
                ·
                  refine ⟨243413108020909503186577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5192812971112736067980309 243413108020909503186577)
                  ·
                    rfl

theorem cell20_533301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_533301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533301 prefixEnd_533301 := by exact prefixLift 533301
  have htrace : WordTrace (prefixWord ++ tailWord_533301) baseStart_533301 baseEnd_533301 := by
    simpa [prefixWord, tailWord_533301, baseEnd_533301] using wordTrace_append hprefix tailTrace_533301
  have hstable : (prefixWord ++ tailWord_533301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533301).length < 2 ^ (prefixWord ++ tailWord_533301).sum := by decide
  have hdescent : baseEnd_533301 < baseStart_533301 := by decide
  rcases family_descends (prefixWord ++ tailWord_533301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533315 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 5]
def baseStart_533315 : Nat := 118140960795 + 533315 * 2 ^ 59
def prefixEnd_533315 : Nat := 4983230072969 + 3 ^ 40 * 533315 * 2
def baseEnd_533315 : Nat := 243419498002387676719853

theorem tailTrace_533315 : CollatzResearch.WordTrace tailWord_533315 prefixEnd_533315 243419498002387676719853 := by
  unfold tailWord_533315
  simp only [CollatzResearch.WordTrace]
  refine ⟨19451596062898312795625399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12967730708598875197083599 19451596062898312795625399)
  ·
    refine ⟨29177394094347469193438099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19451596062898312795625399 29177394094347469193438099)
    ·
      refine ⟨43766091141521203790157149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29177394094347469193438099 43766091141521203790157149)
      ·
        refine ⟨16412284178070451421308931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43766091141521203790157149 16412284178070451421308931)
        ·
          refine ⟨24618426267105677131963397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16412284178070451421308931 24618426267105677131963397)
          ·
            refine ⟨4615954925082314462243137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24618426267105677131963397 4615954925082314462243137)
            ·
              refine ⟨3461966193811735846682353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4615954925082314462243137 3461966193811735846682353)
              ·
                refine ⟨2596474645358801885011765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3461966193811735846682353 2596474645358801885011765)
                ·
                  refine ⟨243419498002387676719853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2596474645358801885011765 243419498002387676719853)
                  ·
                    rfl

theorem cell20_533315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_533315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533315 prefixEnd_533315 := by exact prefixLift 533315
  have htrace : WordTrace (prefixWord ++ tailWord_533315) baseStart_533315 baseEnd_533315 := by
    simpa [prefixWord, tailWord_533315, baseEnd_533315] using wordTrace_append hprefix tailTrace_533315
  have hstable : (prefixWord ++ tailWord_533315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533315).length < 2 ^ (prefixWord ++ tailWord_533315).sum := by decide
  have hdescent : baseEnd_533315 < baseStart_533315 := by decide
  rcases family_descends (prefixWord ++ tailWord_533315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533384 : List Nat := [2, 1, 3, 3, 2, 1, 8]
def baseStart_533384 : Nat := 118140960795 + 533384 * 2 ^ 59
def prefixEnd_533384 : Nat := 4983230072969 + 3 ^ 40 * 533384 * 2
def baseEnd_533384 : Nat := 27050110164725567046619

theorem tailTrace_533384 : CollatzResearch.WordTrace tailWord_533384 prefixEnd_533384 27050110164725567046619 := by
  unfold tailWord_533384
  simp only [CollatzResearch.WordTrace]
  refine ⟨9727056349824168789943603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12969408466432225053258137 9727056349824168789943603)
  ·
    refine ⟨14590584524736253184915405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9727056349824168789943603 14590584524736253184915405)
    ·
      refine ⟨5471469196776094944343277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14590584524736253184915405 5471469196776094944343277)
      ·
        refine ⟨2051800948791035604128729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5471469196776094944343277 2051800948791035604128729)
        ·
          refine ⟨1538850711593276703096547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2051800948791035604128729 1538850711593276703096547)
          ·
            refine ⟨2308276067389915054644821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538850711593276703096547 2308276067389915054644821)
            ·
              refine ⟨27050110164725567046619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2308276067389915054644821 27050110164725567046619)
              ·
                rfl

theorem cell20_533384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 8].length) (baseStart_533384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533384 prefixEnd_533384 := by exact prefixLift 533384
  have htrace : WordTrace (prefixWord ++ tailWord_533384) baseStart_533384 baseEnd_533384 := by
    simpa [prefixWord, tailWord_533384, baseEnd_533384] using wordTrace_append hprefix tailTrace_533384
  have hstable : (prefixWord ++ tailWord_533384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533384).length < 2 ^ (prefixWord ++ tailWord_533384).sum := by decide
  have hdescent : baseEnd_533384 < baseStart_533384 := by decide
  rcases family_descends (prefixWord ++ tailWord_533384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533532 : List Nat := [2, 2, 3, 1, 4, 2, 2, 4]
def baseStart_533532 : Nat := 118140960795 + 533532 * 2 ^ 59
def prefixEnd_533532 : Nat := 4983230072969 + 3 ^ 40 * 533532 * 2
def baseEnd_533532 : Nat := 81172847571766455495211

theorem tailTrace_533532 : CollatzResearch.WordTrace tailWord_533532 prefixEnd_533532 81172847571766455495211 := by
  unfold tailWord_533532
  simp only [CollatzResearch.WordTrace]
  refine ⟨9729755351556079428137425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12973007135408105904183233 9729755351556079428137425)
  ·
    refine ⟨7297316513667059571103069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9729755351556079428137425 7297316513667059571103069)
    ·
      refine ⟨2736493692625147339163651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7297316513667059571103069 2736493692625147339163651)
      ·
        refine ⟨4104740538937721008745477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2736493692625147339163651 4104740538937721008745477)
        ·
          refine ⟨769638851050822689139777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4104740538937721008745477 769638851050822689139777)
          ·
            refine ⟨577229138288117016854833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769638851050822689139777 577229138288117016854833)
            ·
              refine ⟨432921853716087762641125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577229138288117016854833 432921853716087762641125)
              ·
                refine ⟨81172847571766455495211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 432921853716087762641125 81172847571766455495211)
                ·
                  rfl

theorem cell20_533532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_533532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533532 prefixEnd_533532 := by exact prefixLift 533532
  have htrace : WordTrace (prefixWord ++ tailWord_533532) baseStart_533532 baseEnd_533532 := by
    simpa [prefixWord, tailWord_533532, baseEnd_533532] using wordTrace_append hprefix tailTrace_533532
  have hstable : (prefixWord ++ tailWord_533532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533532).length < 2 ^ (prefixWord ++ tailWord_533532).sum := by decide
  have hdescent : baseEnd_533532 < baseStart_533532 := by decide
  rcases family_descends (prefixWord ++ tailWord_533532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533636 : List Nat := [2, 3, 2, 1, 2, 2, 2, 3, 3]
def baseStart_533636 : Nat := 118140960795 + 533636 * 2 ^ 59
def prefixEnd_533636 : Nat := 4983230072969 + 3 ^ 40 * 533636 * 2
def baseEnd_533636 : Nat := 243566011149137227018541

theorem tailTrace_533636 : CollatzResearch.WordTrace tailWord_533636 prefixEnd_533636 243566011149137227018541 := by
  unfold tailWord_533636
  simp only [CollatzResearch.WordTrace]
  refine ⟨9731651947367692309030381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12975535929823589745373841 9731651947367692309030381)
  ·
    refine ⟨3649369480262884615886393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9731651947367692309030381 3649369480262884615886393)
    ·
      refine ⟨2737027110197163461914795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3649369480262884615886393 2737027110197163461914795)
      ·
        refine ⟨4105540665295745192872193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2737027110197163461914795 4105540665295745192872193)
        ·
          refine ⟨3079155498971808894654145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4105540665295745192872193 3079155498971808894654145)
          ·
            refine ⟨2309366624228856670990609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3079155498971808894654145 2309366624228856670990609)
            ·
              refine ⟨1732024968171642503242957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2309366624228856670990609 1732024968171642503242957)
              ·
                refine ⟨649509363064365938716109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1732024968171642503242957 649509363064365938716109)
                ·
                  refine ⟨243566011149137227018541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649509363064365938716109 243566011149137227018541)
                  ·
                    rfl

theorem cell20_533636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_533636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533636 prefixEnd_533636 := by exact prefixLift 533636
  have htrace : WordTrace (prefixWord ++ tailWord_533636) baseStart_533636 baseEnd_533636 := by
    simpa [prefixWord, tailWord_533636, baseEnd_533636] using wordTrace_append hprefix tailTrace_533636
  have hstable : (prefixWord ++ tailWord_533636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533636).length < 2 ^ (prefixWord ++ tailWord_533636).sum := by decide
  have hdescent : baseEnd_533636 < baseStart_533636 := by decide
  rcases family_descends (prefixWord ++ tailWord_533636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533660 : List Nat := [2, 2, 3, 2, 1, 2, 1, 5, 2]
def baseStart_533660 : Nat := 118140960795 + 533660 * 2 ^ 59
def prefixEnd_533660 : Nat := 4983230072969 + 3 ^ 40 * 533660 * 2
def baseEnd_533660 : Nat := 243576965403099810218443

theorem tailTrace_533660 : CollatzResearch.WordTrace tailWord_533660 prefixEnd_533660 243576965403099810218443 := by
  unfold tailWord_533660
  simp only [CollatzResearch.WordTrace]
  refine ⟨9732089623324218358467217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12976119497765624477956289 9732089623324218358467217)
  ·
    refine ⟨7299067217493163768850413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9732089623324218358467217 7299067217493163768850413)
    ·
      refine ⟨2737150206559936413318905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7299067217493163768850413 2737150206559936413318905)
      ·
        refine ⟨2052862654919952309989179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2737150206559936413318905 2052862654919952309989179)
        ·
          refine ⟨3079293982379928464983769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2052862654919952309989179 3079293982379928464983769)
          ·
            refine ⟨2309470486784946348737827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3079293982379928464983769 2309470486784946348737827)
            ·
              refine ⟨3464205730177419523106741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2309470486784946348737827 3464205730177419523106741)
              ·
                refine ⟨324769287204133080291257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3464205730177419523106741 324769287204133080291257)
                ·
                  refine ⟨243576965403099810218443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324769287204133080291257 243576965403099810218443)
                  ·
                    rfl

theorem cell20_533660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_533660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533660 prefixEnd_533660 := by exact prefixLift 533660
  have htrace : WordTrace (prefixWord ++ tailWord_533660) baseStart_533660 baseEnd_533660 := by
    simpa [prefixWord, tailWord_533660, baseEnd_533660] using wordTrace_append hprefix tailTrace_533660
  have hstable : (prefixWord ++ tailWord_533660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533660).length < 2 ^ (prefixWord ++ tailWord_533660).sum := by decide
  have hdescent : baseEnd_533660 < baseStart_533660 := by decide
  rcases family_descends (prefixWord ++ tailWord_533660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533664 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 6]
def baseStart_533664 : Nat := 118140960795 + 533664 * 2 ^ 59
def prefixEnd_533664 : Nat := 4983230072969 + 3 ^ 40 * 533664 * 2
def baseEnd_533664 : Nat := 243578791112093574085093

theorem tailTrace_533664 : CollatzResearch.WordTrace tailWord_533664 prefixEnd_533664 243578791112093574085093 := by
  unfold tailWord_533664
  simp only [CollatzResearch.WordTrace]
  refine ⟨9732162569316972700040023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12976216759089296933386697 9732162569316972700040023)
  ·
    refine ⟨14598243853975459050060035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9732162569316972700040023 14598243853975459050060035)
    ·
      refine ⟨21897365780963188575090053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14598243853975459050060035 21897365780963188575090053)
      ·
        refine ⟨4105756083930597857829385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21897365780963188575090053 4105756083930597857829385)
        ·
          refine ⟨3079317062947948393372039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4105756083930597857829385 3079317062947948393372039)
          ·
            refine ⟨4618975594421922590058059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3079317062947948393372039 4618975594421922590058059)
            ·
              refine ⟨6928463391632883885087089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4618975594421922590058059 6928463391632883885087089)
              ·
                refine ⟨5196347543724662913815317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6928463391632883885087089 5196347543724662913815317)
                ·
                  refine ⟨243578791112093574085093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5196347543724662913815317 243578791112093574085093)
                  ·
                    rfl

theorem cell20_533664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_533664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533664 prefixEnd_533664 := by exact prefixLift 533664
  have htrace : WordTrace (prefixWord ++ tailWord_533664) baseStart_533664 baseEnd_533664 := by
    simpa [prefixWord, tailWord_533664, baseEnd_533664] using wordTrace_append hprefix tailTrace_533664
  have hstable : (prefixWord ++ tailWord_533664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533664).length < 2 ^ (prefixWord ++ tailWord_533664).sum := by decide
  have hdescent : baseEnd_533664 < baseStart_533664 := by decide
  rcases family_descends (prefixWord ++ tailWord_533664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533681 : List Nat := [1, 2, 2, 5, 1, 1, 1, 3, 4]
def baseStart_533681 : Nat := 118140960795 + 533681 * 2 ^ 59
def prefixEnd_533681 : Nat := 4983230072969 + 3 ^ 40 * 533681 * 2
def baseEnd_533681 : Nat := 243586550375317070518357

theorem tailTrace_533681 : CollatzResearch.WordTrace tailWord_533681 prefixEnd_533681 243586550375317070518357 := by
  unfold tailWord_533681
  simp only [CollatzResearch.WordTrace]
  refine ⟨19464945179572357303448897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12976630119714904868965931 19464945179572357303448897)
  ·
    refine ⟨14598708884679267977586673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19464945179572357303448897 14598708884679267977586673)
    ·
      refine ⟨10949031663509450983190005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14598708884679267977586673 10949031663509450983190005)
      ·
        refine ⟨1026471718454011029674063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10949031663509450983190005 1026471718454011029674063)
        ·
          refine ⟨1539707577681016544511095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026471718454011029674063 1539707577681016544511095)
          ·
            refine ⟨2309561366521524816766643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539707577681016544511095 2309561366521524816766643)
            ·
              refine ⟨3464342049782287225149965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2309561366521524816766643 3464342049782287225149965)
              ·
                refine ⟨1299128268668357709431237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3464342049782287225149965 1299128268668357709431237)
                ·
                  refine ⟨243586550375317070518357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1299128268668357709431237 243586550375317070518357)
                  ·
                    rfl

theorem cell20_533681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_533681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533681 prefixEnd_533681 := by exact prefixLift 533681
  have htrace : WordTrace (prefixWord ++ tailWord_533681) baseStart_533681 baseEnd_533681 := by
    simpa [prefixWord, tailWord_533681, baseEnd_533681] using wordTrace_append hprefix tailTrace_533681
  have hstable : (prefixWord ++ tailWord_533681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533681).length < 2 ^ (prefixWord ++ tailWord_533681).sum := by decide
  have hdescent : baseEnd_533681 < baseStart_533681 := by decide
  rcases family_descends (prefixWord ++ tailWord_533681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533695 : List Nat := [1, 1, 2, 2, 2, 2, 2, 5, 3]
def baseStart_533695 : Nat := 118140960795 + 533695 * 2 ^ 59
def prefixEnd_533695 : Nat := 4983230072969 + 3 ^ 40 * 533695 * 2
def baseEnd_533695 : Nat := 243592940356795244051633

theorem tailTrace_533695 : CollatzResearch.WordTrace tailWord_533695 prefixEnd_533695 243592940356795244051633 := by
  unfold tailWord_533695
  simp only [CollatzResearch.WordTrace]
  refine ⟨19465455801521637694458539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12976970534347758462972359 19465455801521637694458539)
  ·
    refine ⟨29198183702282456541687809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19465455801521637694458539 29198183702282456541687809)
    ·
      refine ⟨21898637776711842406265857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29198183702282456541687809 21898637776711842406265857)
      ·
        refine ⟨16423978332533881804699393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21898637776711842406265857 16423978332533881804699393)
        ·
          refine ⟨12317983749400411353524545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16423978332533881804699393 12317983749400411353524545)
          ·
            refine ⟨9238487812050308515143409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12317983749400411353524545 9238487812050308515143409)
            ·
              refine ⟨6928865859037731386357557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9238487812050308515143409 6928865859037731386357557)
              ·
                refine ⟨649581174284787317471021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6928865859037731386357557 649581174284787317471021)
                ·
                  refine ⟨243592940356795244051633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649581174284787317471021 243592940356795244051633)
                  ·
                    rfl

theorem cell20_533695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 3].length) (baseStart_533695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533695 prefixEnd_533695 := by exact prefixLift 533695
  have htrace : WordTrace (prefixWord ++ tailWord_533695) baseStart_533695 baseEnd_533695 := by
    simpa [prefixWord, tailWord_533695, baseEnd_533695] using wordTrace_append hprefix tailTrace_533695
  have hstable : (prefixWord ++ tailWord_533695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533695).length < 2 ^ (prefixWord ++ tailWord_533695).sum := by decide
  have hdescent : baseEnd_533695 < baseStart_533695 := by decide
  rcases family_descends (prefixWord ++ tailWord_533695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533746 : List Nat := [3, 2, 1, 3, 3, 2, 2, 1, 3]
def baseStart_533746 : Nat := 118140960795 + 533746 * 2 ^ 59
def prefixEnd_533746 : Nat := 4983230072969 + 3 ^ 40 * 533746 * 2
def baseEnd_533746 : Nat := 243616218146465733351425

theorem tailTrace_533746 : CollatzResearch.WordTrace tailWord_533746 prefixEnd_533746 243616218146465733351425 := by
  unfold tailWord_533746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4866828981084218351141273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12978210616224582269710061 4866828981084218351141273)
  ·
    refine ⟨3650121735813163763355955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4866828981084218351141273 3650121735813163763355955)
    ·
      refine ⟨5475182603719745645033933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3650121735813163763355955 5475182603719745645033933)
      ·
        refine ⟨2053193476394904616887725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5475182603719745645033933 2053193476394904616887725)
        ·
          refine ⟨769947553648089231332897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2053193476394904616887725 769947553648089231332897)
          ·
            refine ⟨577460665236066923499673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769947553648089231332897 577460665236066923499673)
            ·
              refine ⟨433095498927050192624755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577460665236066923499673 433095498927050192624755)
              ·
                refine ⟨649643248390575288937133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433095498927050192624755 649643248390575288937133)
                ·
                  refine ⟨243616218146465733351425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649643248390575288937133 243616218146465733351425)
                  ·
                    rfl

theorem cell20_533746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_533746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533746 prefixEnd_533746 := by exact prefixLift 533746
  have htrace : WordTrace (prefixWord ++ tailWord_533746) baseStart_533746 baseEnd_533746 := by
    simpa [prefixWord, tailWord_533746, baseEnd_533746] using wordTrace_append hprefix tailTrace_533746
  have hstable : (prefixWord ++ tailWord_533746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533746).length < 2 ^ (prefixWord ++ tailWord_533746).sum := by decide
  have hdescent : baseEnd_533746 < baseStart_533746 := by decide
  rcases family_descends (prefixWord ++ tailWord_533746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533747 : List Nat := [1, 1, 1, 2, 2, 5, 1, 7]
def baseStart_533747 : Nat := 118140960795 + 533747 * 2 ^ 59
def prefixEnd_533747 : Nat := 4983230072969 + 3 ^ 40 * 533747 * 2
def baseEnd_533747 : Nat := 81205558191238058106029

theorem tailTrace_533747 : CollatzResearch.WordTrace tailWord_533747 prefixEnd_533747 81205558191238058106029 := by
  unfold tailWord_533747
  simp only [CollatzResearch.WordTrace]
  refine ⟨19467352397333250575351495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12978234931555500383567663 19467352397333250575351495)
  ·
    refine ⟨29201028595999875863027243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19467352397333250575351495 29201028595999875863027243)
    ·
      refine ⟨43801542893999813794540865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29201028595999875863027243 43801542893999813794540865)
      ·
        refine ⟨32851157170499860345905649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43801542893999813794540865 32851157170499860345905649)
        ·
          refine ⟨24638367877874895259429237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32851157170499860345905649 24638367877874895259429237)
          ·
            refine ⟨2309846988550771430571491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24638367877874895259429237 2309846988550771430571491)
            ·
              refine ⟨3464770482826157145857237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2309846988550771430571491 3464770482826157145857237)
              ·
                refine ⟨81205558191238058106029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3464770482826157145857237 81205558191238058106029)
                ·
                  rfl

theorem cell20_533747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 7].length) (baseStart_533747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533747 prefixEnd_533747 := by exact prefixLift 533747
  have htrace : WordTrace (prefixWord ++ tailWord_533747) baseStart_533747 baseEnd_533747 := by
    simpa [prefixWord, tailWord_533747, baseEnd_533747] using wordTrace_append hprefix tailTrace_533747
  have hstable : (prefixWord ++ tailWord_533747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533747).length < 2 ^ (prefixWord ++ tailWord_533747).sum := by decide
  have hdescent : baseEnd_533747 < baseStart_533747 := by decide
  rcases family_descends (prefixWord ++ tailWord_533747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533764 : List Nat := [2, 3, 2, 2, 2, 1, 2, 6]
def baseStart_533764 : Nat := 118140960795 + 533764 * 2 ^ 59
def prefixEnd_533764 : Nat := 4983230072969 + 3 ^ 40 * 533764 * 2
def baseEnd_533764 : Nat := 81208144612312556917117

theorem tailTrace_533764 : CollatzResearch.WordTrace tailWord_533764 prefixEnd_533764 81208144612312556917117 := by
  unfold tailWord_533764
  simp only [CollatzResearch.WordTrace]
  refine ⟨9733986219135831239360173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12978648292181108319146897 9733986219135831239360173)
  ·
    refine ⟨3650244832175936714760065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9733986219135831239360173 3650244832175936714760065)
    ·
      refine ⟨2737683624131952536070049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3650244832175936714760065 2737683624131952536070049)
      ·
        refine ⟨2053262718098964402052537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2737683624131952536070049 2053262718098964402052537)
        ·
          refine ⟨1539947038574223301539403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2053262718098964402052537 1539947038574223301539403)
          ·
            refine ⟨2309920557861334952309105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539947038574223301539403 2309920557861334952309105)
            ·
              refine ⟨1732440418396001214231829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2309920557861334952309105 1732440418396001214231829)
              ·
                refine ⟨81208144612312556917117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1732440418396001214231829 81208144612312556917117)
                ·
                  rfl

theorem cell20_533764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_533764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533764 prefixEnd_533764 := by exact prefixLift 533764
  have htrace : WordTrace (prefixWord ++ tailWord_533764) baseStart_533764 baseEnd_533764 := by
    simpa [prefixWord, tailWord_533764, baseEnd_533764] using wordTrace_append hprefix tailTrace_533764
  have hstable : (prefixWord ++ tailWord_533764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533764).length < 2 ^ (prefixWord ++ tailWord_533764).sum := by decide
  have hdescent : baseEnd_533764 < baseStart_533764 := by decide
  rcases family_descends (prefixWord ++ tailWord_533764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533805 : List Nat := [1, 5, 3, 1, 1, 1, 2, 3, 3]
def baseStart_533805 : Nat := 118140960795 + 533805 * 2 ^ 59
def prefixEnd_533805 : Nat := 4983230072969 + 3 ^ 40 * 533805 * 2
def baseEnd_533805 : Nat := 243643147354123750384517

theorem tailTrace_533805 : CollatzResearch.WordTrace tailWord_533805 prefixEnd_533805 243643147354123750384517 := by
  unfold tailWord_533805
  simp only [CollatzResearch.WordTrace]
  refine ⟨19469467831123126480962869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12979645220748750987308579 19469467831123126480962869)
  ·
    refine ⟨1825262609167793107590269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19469467831123126480962869 1825262609167793107590269)
    ·
      refine ⟨684473478437922415346351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1825262609167793107590269 684473478437922415346351)
      ·
        refine ⟨1026710217656883623019527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684473478437922415346351 1026710217656883623019527)
        ·
          refine ⟨1540065326485325434529291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026710217656883623019527 1540065326485325434529291)
          ·
            refine ⟨2310097989727988151793937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540065326485325434529291 2310097989727988151793937)
            ·
              refine ⟨1732573492295991113845453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2310097989727988151793937 1732573492295991113845453)
              ·
                refine ⟨649715059610996667692045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1732573492295991113845453 649715059610996667692045)
                ·
                  refine ⟨243643147354123750384517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649715059610996667692045 243643147354123750384517)
                  ·
                    rfl

theorem cell20_533805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_533805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533805 prefixEnd_533805 := by exact prefixLift 533805
  have htrace : WordTrace (prefixWord ++ tailWord_533805) baseStart_533805 baseEnd_533805 := by
    simpa [prefixWord, tailWord_533805, baseEnd_533805] using wordTrace_append hprefix tailTrace_533805
  have hstable : (prefixWord ++ tailWord_533805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533805).length < 2 ^ (prefixWord ++ tailWord_533805).sum := by decide
  have hdescent : baseEnd_533805 < baseStart_533805 := by decide
  rcases family_descends (prefixWord ++ tailWord_533805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533833 : List Nat := [1, 2, 1, 1, 2, 3, 3, 5, 2]
def baseStart_533833 : Nat := 118140960795 + 533833 * 2 ^ 59
def prefixEnd_533833 : Nat := 4983230072969 + 3 ^ 40 * 533833 * 2
def baseEnd_533833 : Nat := 243655927317080097451069

theorem tailTrace_533833 : CollatzResearch.WordTrace tailWord_533833 prefixEnd_533833 243655927317080097451069 := by
  unfold tailWord_533833
  simp only [CollatzResearch.WordTrace]
  refine ⟨19470489075021687262982153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12980326050014458175321435 19470489075021687262982153)
  ·
    refine ⟨14602866806266265447236615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19470489075021687262982153 14602866806266265447236615)
    ·
      refine ⟨21904300209399398170854923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14602866806266265447236615 21904300209399398170854923)
      ·
        refine ⟨32856450314099097256282385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21904300209399398170854923 32856450314099097256282385)
        ·
          refine ⟨24642337735574322942211789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32856450314099097256282385 24642337735574322942211789)
          ·
            refine ⟨9240876650840371103329421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24642337735574322942211789 9240876650840371103329421)
            ·
              refine ⟨3465328744065139163748533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9240876650840371103329421 3465328744065139163748533)
              ·
                refine ⟨324874569756106796601425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3465328744065139163748533 324874569756106796601425)
                ·
                  refine ⟨243655927317080097451069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324874569756106796601425 243655927317080097451069)
                  ·
                    rfl

theorem cell20_533833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 2].length) (baseStart_533833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533833 prefixEnd_533833 := by exact prefixLift 533833
  have htrace : WordTrace (prefixWord ++ tailWord_533833) baseStart_533833 baseEnd_533833 := by
    simpa [prefixWord, tailWord_533833, baseEnd_533833] using wordTrace_append hprefix tailTrace_533833
  have hstable : (prefixWord ++ tailWord_533833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533833).length < 2 ^ (prefixWord ++ tailWord_533833).sum := by decide
  have hdescent : baseEnd_533833 < baseStart_533833 := by decide
  rcases family_descends (prefixWord ++ tailWord_533833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533847 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 5]
def baseStart_533847 : Nat := 118140960795 + 533847 * 2 ^ 59
def prefixEnd_533847 : Nat := 4983230072969 + 3 ^ 40 * 533847 * 2
def baseEnd_533847 : Nat := 243662317298558270984345

theorem tailTrace_533847 : CollatzResearch.WordTrace tailWord_533847 prefixEnd_533847 243662317298558270984345 := by
  unfold tailWord_533847
  simp only [CollatzResearch.WordTrace]
  refine ⟨19470999696970967653991795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12980666464647311769327863 19470999696970967653991795)
  ·
    refine ⟨29206499545456451480987693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19470999696970967653991795 29206499545456451480987693)
    ·
      refine ⟨10952437329546169305370385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29206499545456451480987693 10952437329546169305370385)
      ·
        refine ⟨8214327997159626979027789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10952437329546169305370385 8214327997159626979027789)
        ·
          refine ⟨3080372998934860117135421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8214327997159626979027789 3080372998934860117135421)
          ·
            refine ⟨1155139874600572543925783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3080372998934860117135421 1155139874600572543925783)
            ·
              refine ⟨1732709811900858815888675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155139874600572543925783 1732709811900858815888675)
              ·
                refine ⟨2599064717851288223833013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1732709811900858815888675 2599064717851288223833013)
                ·
                  refine ⟨243662317298558270984345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2599064717851288223833013 243662317298558270984345)
                  ·
                    rfl

theorem cell20_533847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 5].length) (baseStart_533847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533847 prefixEnd_533847 := by exact prefixLift 533847
  have htrace : WordTrace (prefixWord ++ tailWord_533847) baseStart_533847 baseEnd_533847 := by
    simpa [prefixWord, tailWord_533847, baseEnd_533847] using wordTrace_append hprefix tailTrace_533847
  have hstable : (prefixWord ++ tailWord_533847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533847).length < 2 ^ (prefixWord ++ tailWord_533847).sum := by decide
  have hdescent : baseEnd_533847 < baseStart_533847 := by decide
  rcases family_descends (prefixWord ++ tailWord_533847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533861 : List Nat := [1, 3, 1, 3, 1, 2, 2, 7]
def baseStart_533861 : Nat := 118140960795 + 533861 * 2 ^ 59
def prefixEnd_533861 : Nat := 4983230072969 + 3 ^ 40 * 533861 * 2
def baseEnd_533861 : Nat := 81222902426678814839207

theorem tailTrace_533861 : CollatzResearch.WordTrace tailWord_533861 prefixEnd_533861 81222902426678814839207 := by
  unfold tailWord_533861
  simp only [CollatzResearch.WordTrace]
  refine ⟨19471510318920248045001437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12981006879280165363334291 19471510318920248045001437)
  ·
    refine ⟨7301816369595093016875539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19471510318920248045001437 7301816369595093016875539)
    ·
      refine ⟨10952724554392639525313309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7301816369595093016875539 10952724554392639525313309)
      ·
        refine ⟨4107271707897239821992491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10952724554392639525313309 4107271707897239821992491)
        ·
          refine ⟨6160907561845859732988737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4107271707897239821992491 6160907561845859732988737)
          ·
            refine ⟨4620680671384394799741553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6160907561845859732988737 4620680671384394799741553)
            ·
              refine ⟨3465510503538296099806165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4620680671384394799741553 3465510503538296099806165)
              ·
                refine ⟨81222902426678814839207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3465510503538296099806165 81222902426678814839207)
                ·
                  rfl

theorem cell20_533861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 7].length) (baseStart_533861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533861 prefixEnd_533861 := by exact prefixLift 533861
  have htrace : WordTrace (prefixWord ++ tailWord_533861) baseStart_533861 baseEnd_533861 := by
    simpa [prefixWord, tailWord_533861, baseEnd_533861] using wordTrace_append hprefix tailTrace_533861
  have hstable : (prefixWord ++ tailWord_533861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533861).length < 2 ^ (prefixWord ++ tailWord_533861).sum := by decide
  have hdescent : baseEnd_533861 < baseStart_533861 := by decide
  rcases family_descends (prefixWord ++ tailWord_533861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533909 : List Nat := [1, 3, 2, 1, 1, 2, 2, 6, 2]
def baseStart_533909 : Nat := 118140960795 + 533909 * 2 ^ 59
def prefixEnd_533909 : Nat := 4983230072969 + 3 ^ 40 * 533909 * 2
def baseEnd_533909 : Nat := 243690615787961610917425

theorem tailTrace_533909 : CollatzResearch.WordTrace tailWord_533909 prefixEnd_533909 243690615787961610917425 := by
  unfold tailWord_533909
  simp only [CollatzResearch.WordTrace]
  refine ⟨19473261022746352242748781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12982174015164234828499187 19473261022746352242748781)
  ·
    refine ⟨7302472883529882091030793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19473261022746352242748781 7302472883529882091030793)
    ·
      refine ⟨5476854662647411568273095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7302472883529882091030793 5476854662647411568273095)
      ·
        refine ⟨8215281993971117352409643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5476854662647411568273095 8215281993971117352409643)
        ·
          refine ⟨12322922990956676028614465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8215281993971117352409643 12322922990956676028614465)
          ·
            refine ⟨9242192243217507021460849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12322922990956676028614465 9242192243217507021460849)
            ·
              refine ⟨6931644182413130266095637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9242192243217507021460849 6931644182413130266095637)
              ·
                refine ⟨324920821050615481223233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6931644182413130266095637 324920821050615481223233)
                ·
                  refine ⟨243690615787961610917425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324920821050615481223233 243690615787961610917425)
                  ·
                    rfl

theorem cell20_533909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_533909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533909 prefixEnd_533909 := by exact prefixLift 533909
  have htrace : WordTrace (prefixWord ++ tailWord_533909) baseStart_533909 baseEnd_533909 := by
    simpa [prefixWord, tailWord_533909, baseEnd_533909] using wordTrace_append hprefix tailTrace_533909
  have hstable : (prefixWord ++ tailWord_533909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533909).length < 2 ^ (prefixWord ++ tailWord_533909).sum := by decide
  have hdescent : baseEnd_533909 < baseStart_533909 := by decide
  rcases family_descends (prefixWord ++ tailWord_533909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533919 : List Nat := [1, 1, 2, 5, 1, 4, 2, 1, 3]
def baseStart_533919 : Nat := 118140960795 + 533919 * 2 ^ 59
def prefixEnd_533919 : Nat := 4983230072969 + 3 ^ 40 * 533919 * 2
def baseEnd_533919 : Nat := 243695180060446020584051

theorem tailTrace_533919 : CollatzResearch.WordTrace tailWord_533919 prefixEnd_533919 243695180060446020584051 := by
  unfold tailWord_533919
  simp only [CollatzResearch.WordTrace]
  refine ⟨19473625752710123950612811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12982417168473415967075207 19473625752710123950612811)
  ·
    refine ⟨29210438629065185925919217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19473625752710123950612811 29210438629065185925919217)
    ·
      refine ⟨21907828971798889444439413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29210438629065185925919217 21907828971798889444439413)
      ·
        refine ⟨2053858966106145885416195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21907828971798889444439413 2053858966106145885416195)
        ·
          refine ⟨3080788449159218828124293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2053858966106145885416195 3080788449159218828124293)
          ·
            refine ⟨577647834217353530273305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3080788449159218828124293 577647834217353530273305)
            ·
              refine ⟨433235875663015147704979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577647834217353530273305 433235875663015147704979)
              ·
                refine ⟨649853813494522721557469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433235875663015147704979 649853813494522721557469)
                ·
                  refine ⟨243695180060446020584051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649853813494522721557469 243695180060446020584051)
                  ·
                    rfl

theorem cell20_533919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 3].length) (baseStart_533919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533919 prefixEnd_533919 := by exact prefixLift 533919
  have htrace : WordTrace (prefixWord ++ tailWord_533919) baseStart_533919 baseEnd_533919 := by
    simpa [prefixWord, tailWord_533919, baseEnd_533919] using wordTrace_append hprefix tailTrace_533919
  have hstable : (prefixWord ++ tailWord_533919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533919).length < 2 ^ (prefixWord ++ tailWord_533919).sum := by decide
  have hdescent : baseEnd_533919 < baseStart_533919 := by decide
  rcases family_descends (prefixWord ++ tailWord_533919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533923 : List Nat := [1, 1, 1, 4, 1, 3, 3, 3, 3]
def baseStart_533923 : Nat := 118140960795 + 533923 * 2 ^ 59
def prefixEnd_533923 : Nat := 4983230072969 + 3 ^ 40 * 533923 * 2
def baseEnd_533923 : Nat := 243697005769439784450701

theorem tailTrace_533923 : CollatzResearch.WordTrace tailWord_533923 prefixEnd_533923 243697005769439784450701 := by
  unfold tailWord_533923
  simp only [CollatzResearch.WordTrace]
  refine ⟨19473771644695632633758423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12982514429797088422505615 19473771644695632633758423)
  ·
    refine ⟨29210657467043448950637635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19473771644695632633758423 29210657467043448950637635)
    ·
      refine ⟨43815986200565173425956453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29210657467043448950637635 43815986200565173425956453)
      ·
        refine ⟨8215497412605970017366835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43815986200565173425956453 8215497412605970017366835)
        ·
          refine ⟨12323246118908955026050253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8215497412605970017366835 12323246118908955026050253)
          ·
            refine ⟨4621217294590858134768845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12323246118908955026050253 4621217294590858134768845)
            ·
              refine ⟨1732956485471571800538317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4621217294590858134768845 1732956485471571800538317)
              ·
                refine ⟨649858682051839425201869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1732956485471571800538317 649858682051839425201869)
                ·
                  refine ⟨243697005769439784450701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649858682051839425201869 243697005769439784450701)
                  ·
                    rfl

theorem cell20_533923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 3].length) (baseStart_533923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533923 prefixEnd_533923 := by exact prefixLift 533923
  have htrace : WordTrace (prefixWord ++ tailWord_533923) baseStart_533923 baseEnd_533923 := by
    simpa [prefixWord, tailWord_533923, baseEnd_533923] using wordTrace_append hprefix tailTrace_533923
  have hstable : (prefixWord ++ tailWord_533923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533923).length < 2 ^ (prefixWord ++ tailWord_533923).sum := by decide
  have hdescent : baseEnd_533923 < baseStart_533923 := by decide
  rcases family_descends (prefixWord ++ tailWord_533923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533937 : List Nat := [1, 2, 2, 4, 1, 1, 1, 8]
def baseStart_533937 : Nat := 118140960795 + 533937 * 2 ^ 59
def prefixEnd_533937 : Nat := 4983230072969 + 3 ^ 40 * 533937 * 2
def baseEnd_533937 : Nat := 81234465250305985994659

theorem tailTrace_533937 : CollatzResearch.WordTrace tailWord_533937 prefixEnd_533937 81234465250305985994659 := by
  unfold tailWord_533937
  simp only [CollatzResearch.WordTrace]
  refine ⟨19474282266644913024768065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12982854844429942016512043 19474282266644913024768065)
  ·
    refine ⟨14605711699983684768576049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19474282266644913024768065 14605711699983684768576049)
    ·
      refine ⟨10954283774987763576432037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14605711699983684768576049 10954283774987763576432037)
      ·
        refine ⟨2053928207810205670581007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10954283774987763576432037 2053928207810205670581007)
        ·
          refine ⟨3080892311715308505871511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2053928207810205670581007 3080892311715308505871511)
          ·
            refine ⟨4621338467572962758807267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3080892311715308505871511 4621338467572962758807267)
            ·
              refine ⟨6932007701359444138210901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4621338467572962758807267 6932007701359444138210901)
              ·
                refine ⟨81234465250305985994659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6932007701359444138210901 81234465250305985994659)
                ·
                  rfl

theorem cell20_533937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 8].length) (baseStart_533937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533937 prefixEnd_533937 := by exact prefixLift 533937
  have htrace : WordTrace (prefixWord ++ tailWord_533937) baseStart_533937 baseEnd_533937 := by
    simpa [prefixWord, tailWord_533937, baseEnd_533937] using wordTrace_append hprefix tailTrace_533937
  have hstable : (prefixWord ++ tailWord_533937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533937).length < 2 ^ (prefixWord ++ tailWord_533937).sum := by decide
  have hdescent : baseEnd_533937 < baseStart_533937 := by decide
  rcases family_descends (prefixWord ++ tailWord_533937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533944 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 7]
def baseStart_533944 : Nat := 118140960795 + 533944 * 2 ^ 59
def prefixEnd_533944 : Nat := 4983230072969 + 3 ^ 40 * 533944 * 2
def baseEnd_533944 : Nat := 243706590741657044750615

theorem tailTrace_533944 : CollatzResearch.WordTrace tailWord_533944 prefixEnd_533944 243706590741657044750615 := by
  unfold tailWord_533944
  simp only [CollatzResearch.WordTrace]
  refine ⟨9737268788809776610136443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12983025051746368813515257 9737268788809776610136443)
  ·
    refine ⟨14605903183214664915204665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9737268788809776610136443 14605903183214664915204665)
    ·
      refine ⟨10954427387410998686403499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14605903183214664915204665 10954427387410998686403499)
      ·
        refine ⟨16431641081116498029605249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10954427387410998686403499 16431641081116498029605249)
        ·
          refine ⟨12323730810837373522203937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16431641081116498029605249 12323730810837373522203937)
          ·
            refine ⟨9242798108128030141652953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12323730810837373522203937 9242798108128030141652953)
            ·
              refine ⟨6932098581096022606239715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9242798108128030141652953 6932098581096022606239715)
              ·
                refine ⟨10398147871644033909359573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6932098581096022606239715 10398147871644033909359573)
                ·
                  refine ⟨243706590741657044750615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10398147871644033909359573 243706590741657044750615)
                  ·
                    rfl

theorem cell20_533944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_533944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533944 prefixEnd_533944 := by exact prefixLift 533944
  have htrace : WordTrace (prefixWord ++ tailWord_533944) baseStart_533944 baseEnd_533944 := by
    simpa [prefixWord, tailWord_533944, baseEnd_533944] using wordTrace_append hprefix tailTrace_533944
  have hstable : (prefixWord ++ tailWord_533944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533944).length < 2 ^ (prefixWord ++ tailWord_533944).sum := by decide
  have hdescent : baseEnd_533944 < baseStart_533944 := by decide
  rcases family_descends (prefixWord ++ tailWord_533944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533964 : List Nat := [2, 2, 1, 4, 2, 2, 1, 4, 2]
def baseStart_533964 : Nat := 118140960795 + 533964 * 2 ^ 59
def prefixEnd_533964 : Nat := 4983230072969 + 3 ^ 40 * 533964 * 2
def baseEnd_533964 : Nat := 243715719286625864083867

theorem tailTrace_533964 : CollatzResearch.WordTrace tailWord_533964 prefixEnd_533964 243715719286625864083867 := by
  unfold tailWord_533964
  simp only [CollatzResearch.WordTrace]
  refine ⟨9737633518773548318000473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12983511358364731090667297 9737633518773548318000473)
  ·
    refine ⟨7303225139080161238500355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9737633518773548318000473 7303225139080161238500355)
    ·
      refine ⟨10954837708620241857750533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7303225139080161238500355 10954837708620241857750533)
      ·
        refine ⟨2054032070366295348328225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10954837708620241857750533 2054032070366295348328225)
        ·
          refine ⟨1540524052774721511246169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2054032070366295348328225 1540524052774721511246169)
          ·
            refine ⟨1155393039581041133434627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1540524052774721511246169 1155393039581041133434627)
            ·
              refine ⟨1733089559371561700151941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155393039581041133434627 1733089559371561700151941)
              ·
                refine ⟨324954292382167818778489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1733089559371561700151941 324954292382167818778489)
                ·
                  refine ⟨243715719286625864083867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324954292382167818778489 243715719286625864083867)
                  ·
                    rfl

theorem cell20_533964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_533964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533964 prefixEnd_533964 := by exact prefixLift 533964
  have htrace : WordTrace (prefixWord ++ tailWord_533964) baseStart_533964 baseEnd_533964 := by
    simpa [prefixWord, tailWord_533964, baseEnd_533964] using wordTrace_append hprefix tailTrace_533964
  have hstable : (prefixWord ++ tailWord_533964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533964).length < 2 ^ (prefixWord ++ tailWord_533964).sum := by decide
  have hdescent : baseEnd_533964 < baseStart_533964 := by decide
  rcases family_descends (prefixWord ++ tailWord_533964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533992 : List Nat := [2, 1, 4, 1, 1, 2, 5, 4]
def baseStart_533992 : Nat := 118140960795 + 533992 * 2 ^ 59
def prefixEnd_533992 : Nat := 4983230072969 + 3 ^ 40 * 533992 * 2
def baseEnd_533992 : Nat := 81242833083194070383473

theorem tailTrace_533992 : CollatzResearch.WordTrace tailWord_533992 prefixEnd_533992 81242833083194070383473 := by
  unfold tailWord_533992
  simp only [CollatzResearch.WordTrace]
  refine ⟨9738144140722828709010115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12984192187630438278680153 9738144140722828709010115)
  ·
    refine ⟨14607216211084243063515173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9738144140722828709010115 14607216211084243063515173)
    ·
      refine ⟨2738853039578295574409095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14607216211084243063515173 2738853039578295574409095)
      ·
        refine ⟨4108279559367443361613643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2738853039578295574409095 4108279559367443361613643)
        ·
          refine ⟨6162419339051165042420465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4108279559367443361613643 6162419339051165042420465)
          ·
            refine ⟨4621814504288373781815349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6162419339051165042420465 4621814504288373781815349)
            ·
              refine ⟨433295109777035042045189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4621814504288373781815349 433295109777035042045189)
              ·
                refine ⟨81242833083194070383473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 433295109777035042045189 81242833083194070383473)
                ·
                  rfl

theorem cell20_533992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_533992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_533992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_533992 prefixEnd_533992 := by exact prefixLift 533992
  have htrace : WordTrace (prefixWord ++ tailWord_533992) baseStart_533992 baseEnd_533992 := by
    simpa [prefixWord, tailWord_533992, baseEnd_533992] using wordTrace_append hprefix tailTrace_533992
  have hstable : (prefixWord ++ tailWord_533992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533992).length < 2 ^ (prefixWord ++ tailWord_533992).sum := by decide
  have hdescent : baseEnd_533992 < baseStart_533992 := by decide
  rcases family_descends (prefixWord ++ tailWord_533992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534002 : List Nat := [3, 2, 1, 4, 1, 1, 1, 5, 2]
def baseStart_534002 : Nat := 118140960795 + 534002 * 2 ^ 59
def prefixEnd_534002 : Nat := 4983230072969 + 3 ^ 40 * 534002 * 2
def baseEnd_534002 : Nat := 243733063522066620817045

theorem tailTrace_534002 : CollatzResearch.WordTrace tailWord_534002 prefixEnd_534002 243733063522066620817045 := by
  unfold tailWord_534002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4869163252852357281471065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12984435340939619417256173 4869163252852357281471065)
  ·
    refine ⟨3651872439639267961103299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4869163252852357281471065 3651872439639267961103299)
    ·
      refine ⟨5477808659458901941654949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3651872439639267961103299 5477808659458901941654949)
      ·
        refine ⟨1027089123648544114060303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5477808659458901941654949 1027089123648544114060303)
        ·
          refine ⟨1540633685472816171090455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027089123648544114060303 1540633685472816171090455)
          ·
            refine ⟨2310950528209224256635683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540633685472816171090455 2310950528209224256635683)
            ·
              refine ⟨3466425792313836384953525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2310950528209224256635683 3466425792313836384953525)
              ·
                refine ⟨324977418029422161089393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3466425792313836384953525 324977418029422161089393)
                ·
                  refine ⟨243733063522066620817045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324977418029422161089393 243733063522066620817045)
                  ·
                    rfl

theorem cell20_534002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_534002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534002 prefixEnd_534002 := by exact prefixLift 534002
  have htrace : WordTrace (prefixWord ++ tailWord_534002) baseStart_534002 baseEnd_534002 := by
    simpa [prefixWord, tailWord_534002, baseEnd_534002] using wordTrace_append hprefix tailTrace_534002
  have hstable : (prefixWord ++ tailWord_534002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534002).length < 2 ^ (prefixWord ++ tailWord_534002).sum := by decide
  have hdescent : baseEnd_534002 < baseStart_534002 := by decide
  rcases family_descends (prefixWord ++ tailWord_534002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534013 : List Nat := [1, 4, 1, 1, 1, 5, 7]
def baseStart_534013 : Nat := 118140960795 + 534013 * 2 ^ 59
def prefixEnd_534013 : Nat := 4983230072969 + 3 ^ 40 * 534013 * 2
def baseEnd_534013 : Nat := 27082009357977719050037

theorem tailTrace_534013 : CollatzResearch.WordTrace tailWord_534013 prefixEnd_534013 27082009357977719050037 := by
  unfold tailWord_534013
  simp only [CollatzResearch.WordTrace]
  refine ⟨19477054214369578004534693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12984702809579718669689795 19477054214369578004534693)
  ·
    refine ⟨3651947665194295875850255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19477054214369578004534693 3651947665194295875850255)
    ·
      refine ⟨5477921497791443813775383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3651947665194295875850255 5477921497791443813775383)
      ·
        refine ⟨8216882246687165720663075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5477921497791443813775383 8216882246687165720663075)
        ·
          refine ⟨12325323370030748580994613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8216882246687165720663075 12325323370030748580994613)
          ·
            refine ⟨1155499065940382679468245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12325323370030748580994613 1155499065940382679468245)
            ·
              refine ⟨27082009357977719050037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1155499065940382679468245 27082009357977719050037)
              ·
                rfl

theorem cell20_534013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 7].length) (baseStart_534013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534013 prefixEnd_534013 := by exact prefixLift 534013
  have htrace : WordTrace (prefixWord ++ tailWord_534013) baseStart_534013 baseEnd_534013 := by
    simpa [prefixWord, tailWord_534013, baseEnd_534013] using wordTrace_append hprefix tailTrace_534013
  have hstable : (prefixWord ++ tailWord_534013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534013).length < 2 ^ (prefixWord ++ tailWord_534013).sum := by decide
  have hdescent : baseEnd_534013 < baseStart_534013 := by decide
  rcases family_descends (prefixWord ++ tailWord_534013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534023 : List Nat := [1, 1, 4, 3, 2, 2, 2, 1, 4]
def baseStart_534023 : Nat := 118140960795 + 534023 * 2 ^ 59
def prefixEnd_534023 : Nat := 4983230072969 + 3 ^ 40 * 534023 * 2
def baseEnd_534023 : Nat := 243742648494283881116959

theorem tailTrace_534023 : CollatzResearch.WordTrace tailWord_534023 prefixEnd_534023 243742648494283881116959 := by
  unfold tailWord_534023
  simp only [CollatzResearch.WordTrace]
  refine ⟨19477418944333349712398723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12984945962888899808265815 19477418944333349712398723)
  ·
    refine ⟨29216128416500024568598085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19477418944333349712398723 29216128416500024568598085)
    ·
      refine ⟨5478024078093754606612141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29216128416500024568598085 5478024078093754606612141)
      ·
        refine ⟨2054259029285157977479553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5478024078093754606612141 2054259029285157977479553)
        ·
          refine ⟨1540694271963868483109665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2054259029285157977479553 1540694271963868483109665)
          ·
            refine ⟨1155520703972901362332249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1540694271963868483109665 1155520703972901362332249)
            ·
              refine ⟨866640527979676021749187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1155520703972901362332249 866640527979676021749187)
              ·
                refine ⟨1299960791969514032623781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866640527979676021749187 1299960791969514032623781)
                ·
                  refine ⟨243742648494283881116959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1299960791969514032623781 243742648494283881116959)
                  ·
                    rfl

theorem cell20_534023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 4].length) (baseStart_534023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534023 prefixEnd_534023 := by exact prefixLift 534023
  have htrace : WordTrace (prefixWord ++ tailWord_534023) baseStart_534023 baseEnd_534023 := by
    simpa [prefixWord, tailWord_534023, baseEnd_534023] using wordTrace_append hprefix tailTrace_534023
  have hstable : (prefixWord ++ tailWord_534023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534023).length < 2 ^ (prefixWord ++ tailWord_534023).sum := by decide
  have hdescent : baseEnd_534023 < baseStart_534023 := by decide
  rcases family_descends (prefixWord ++ tailWord_534023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534029 : List Nat := [1, 7, 1, 1, 2, 1, 3, 1, 3]
def baseStart_534029 : Nat := 118140960795 + 534029 * 2 ^ 59
def prefixEnd_534029 : Nat := 4983230072969 + 3 ^ 40 * 534029 * 2
def baseEnd_534029 : Nat := 243745387057774526916935

theorem tailTrace_534029 : CollatzResearch.WordTrace tailWord_534029 prefixEnd_534029 243745387057774526916935 := by
  unfold tailWord_534029
  simp only [CollatzResearch.WordTrace]
  refine ⟨19477637782311612737117141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12985091854874408491411427 19477637782311612737117141)
  ·
    refine ⟨456507135522928423526183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 19477637782311612737117141 456507135522928423526183)
    ·
      refine ⟨684760703284392635289275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456507135522928423526183 684760703284392635289275)
      ·
        refine ⟨1027141054926588952933913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684760703284392635289275 1027141054926588952933913)
        ·
          refine ⟨770355791194941714700435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1027141054926588952933913 770355791194941714700435)
          ·
            refine ⟨1155533686792412572050653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770355791194941714700435 1155533686792412572050653)
            ·
              refine ⟨433325132547154714518995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1155533686792412572050653 433325132547154714518995)
              ·
                refine ⟨649987698820732071778493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433325132547154714518995 649987698820732071778493)
                ·
                  refine ⟨243745387057774526916935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649987698820732071778493 243745387057774526916935)
                  ·
                    rfl

theorem cell20_534029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_534029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534029 prefixEnd_534029 := by exact prefixLift 534029
  have htrace : WordTrace (prefixWord ++ tailWord_534029) baseStart_534029 baseEnd_534029 := by
    simpa [prefixWord, tailWord_534029, baseEnd_534029] using wordTrace_append hprefix tailTrace_534029
  have hstable : (prefixWord ++ tailWord_534029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534029).length < 2 ^ (prefixWord ++ tailWord_534029).sum := by decide
  have hdescent : baseEnd_534029 < baseStart_534029 := by decide
  rcases family_descends (prefixWord ++ tailWord_534029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534044 : List Nat := [2, 2, 3, 1, 2, 1, 1, 4, 4]
def baseStart_534044 : Nat := 118140960795 + 534044 * 2 ^ 59
def prefixEnd_534044 : Nat := 4983230072969 + 3 ^ 40 * 534044 * 2
def baseEnd_534044 : Nat := 243752233466501141416873

theorem tailTrace_534044 : CollatzResearch.WordTrace tailWord_534044 prefixEnd_534044 243752233466501141416873 := by
  unfold tailWord_534044
  simp only [CollatzResearch.WordTrace]
  refine ⟨9739092438628635149456593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12985456584838180199275457 9739092438628635149456593)
  ·
    refine ⟨7304319328971476362092445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9739092438628635149456593 7304319328971476362092445)
    ·
      refine ⟨2739119748364303635784667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7304319328971476362092445 2739119748364303635784667)
      ·
        refine ⟨4108679622546455453677001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2739119748364303635784667 4108679622546455453677001)
        ·
          refine ⟨3081509716909841590257751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4108679622546455453677001 3081509716909841590257751)
          ·
            refine ⟨4622264575364762385386627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3081509716909841590257751 4622264575364762385386627)
            ·
              refine ⟨6933396863047143578079941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4622264575364762385386627 6933396863047143578079941)
              ·
                refine ⟨1300011911821339420889989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6933396863047143578079941 1300011911821339420889989)
                ·
                  refine ⟨243752233466501141416873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1300011911821339420889989 243752233466501141416873)
                  ·
                    rfl

theorem cell20_534044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_534044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534044 prefixEnd_534044 := by exact prefixLift 534044
  have htrace : WordTrace (prefixWord ++ tailWord_534044) baseStart_534044 baseEnd_534044 := by
    simpa [prefixWord, tailWord_534044, baseEnd_534044] using wordTrace_append hprefix tailTrace_534044
  have hstable : (prefixWord ++ tailWord_534044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534044).length < 2 ^ (prefixWord ++ tailWord_534044).sum := by decide
  have hdescent : baseEnd_534044 < baseStart_534044 := by decide
  rcases family_descends (prefixWord ++ tailWord_534044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534092 : List Nat := [2, 2, 1, 3, 1, 3, 4, 1, 3]
def baseStart_534092 : Nat := 118140960795 + 534092 * 2 ^ 59
def prefixEnd_534092 : Nat := 4983230072969 + 3 ^ 40 * 534092 * 2
def baseEnd_534092 : Nat := 243774141974426307816677

theorem tailTrace_534092 : CollatzResearch.WordTrace tailWord_534092 prefixEnd_534092 243774141974426307816677 := by
  unfold tailWord_534092
  simp only [CollatzResearch.WordTrace]
  refine ⟨9739967790541687248330265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12986623720722249664440353 9739967790541687248330265)
  ·
    refine ⟨7304975842906265436247699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9739967790541687248330265 7304975842906265436247699)
    ·
      refine ⟨10957463764359398154371549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7304975842906265436247699 10957463764359398154371549)
      ·
        refine ⟨4109048911634774307889331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10957463764359398154371549 4109048911634774307889331)
        ·
          refine ⟨6163573367452161461833997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4109048911634774307889331 6163573367452161461833997)
          ·
            refine ⟨2311340012794560548187749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6163573367452161461833997 2311340012794560548187749)
            ·
              refine ⟨433376252398980102785203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2311340012794560548187749 433376252398980102785203)
              ·
                refine ⟨650064378598470154177805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433376252398980102785203 650064378598470154177805)
                ·
                  refine ⟨243774141974426307816677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650064378598470154177805 243774141974426307816677)
                  ·
                    rfl

theorem cell20_534092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_534092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534092 prefixEnd_534092 := by exact prefixLift 534092
  have htrace : WordTrace (prefixWord ++ tailWord_534092) baseStart_534092 baseEnd_534092 := by
    simpa [prefixWord, tailWord_534092, baseEnd_534092] using wordTrace_append hprefix tailTrace_534092
  have hstable : (prefixWord ++ tailWord_534092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534092).length < 2 ^ (prefixWord ++ tailWord_534092).sum := by decide
  have hdescent : baseEnd_534092 < baseStart_534092 := by decide
  rcases family_descends (prefixWord ++ tailWord_534092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534130 : List Nat := [3, 2, 1, 2, 3, 2, 2, 2, 3]
def baseStart_534130 : Nat := 118140960795 + 534130 * 2 ^ 59
def prefixEnd_534130 : Nat := 4983230072969 + 3 ^ 40 * 534130 * 2
def baseEnd_534130 : Nat := 243791486209867064549855

theorem tailTrace_534130 : CollatzResearch.WordTrace tailWord_534130 prefixEnd_534130 243791486209867064549855 := by
  unfold tailWord_534130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4870330388736426746635961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12987547703297137991029229 4870330388736426746635961)
  ·
    refine ⟨3652747791552320059976971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4870330388736426746635961 3652747791552320059976971)
    ·
      refine ⟨5479121687328480089965457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3652747791552320059976971 5479121687328480089965457)
      ·
        refine ⟨4109341265496360067474093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5479121687328480089965457 4109341265496360067474093)
        ·
          refine ⟨1541002974561135025302785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4109341265496360067474093 1541002974561135025302785)
          ·
            refine ⟨1155752230920851268977089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1541002974561135025302785 1155752230920851268977089)
            ·
              refine ⟨866814173190638451732817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1155752230920851268977089 866814173190638451732817)
              ·
                refine ⟨650110629892978838799613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 866814173190638451732817 650110629892978838799613)
                ·
                  refine ⟨243791486209867064549855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650110629892978838799613 243791486209867064549855)
                  ·
                    rfl

theorem cell20_534130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_534130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534130 prefixEnd_534130 := by exact prefixLift 534130
  have htrace : WordTrace (prefixWord ++ tailWord_534130) baseStart_534130 baseEnd_534130 := by
    simpa [prefixWord, tailWord_534130, baseEnd_534130] using wordTrace_append hprefix tailTrace_534130
  have hstable : (prefixWord ++ tailWord_534130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534130).length < 2 ^ (prefixWord ++ tailWord_534130).sum := by decide
  have hdescent : baseEnd_534130 < baseStart_534130 := by decide
  rcases family_descends (prefixWord ++ tailWord_534130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534133 : List Nat := [1, 3, 4, 2, 1, 1, 4, 2, 2]
def baseStart_534133 : Nat := 118140960795 + 534133 * 2 ^ 59
def prefixEnd_534133 : Nat := 4983230072969 + 3 ^ 40 * 534133 * 2
def baseEnd_534133 : Nat := 243792855491612387449843

theorem tailTrace_534133 : CollatzResearch.WordTrace tailWord_534133 prefixEnd_534133 243792855491612387449843 := by
  unfold tailWord_534133
  simp only [CollatzResearch.WordTrace]
  refine ⟨19481430973934838498903053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12987620649289892332602035 19481430973934838498903053)
  ·
    refine ⟨7305536615225564437088645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19481430973934838498903053 7305536615225564437088645)
    ·
      refine ⟨1369788115354793331954121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7305536615225564437088645 1369788115354793331954121)
      ·
        refine ⟨1027341086516094998965591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1369788115354793331954121 1027341086516094998965591)
        ·
          refine ⟨1541011629774142498448387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027341086516094998965591 1541011629774142498448387)
          ·
            refine ⟨2311517444661213747672581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1541011629774142498448387 2311517444661213747672581)
            ·
              refine ⟨433409520873977577688609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2311517444661213747672581 433409520873977577688609)
              ·
                refine ⟨325057140655483183266457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433409520873977577688609 325057140655483183266457)
                ·
                  refine ⟨243792855491612387449843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325057140655483183266457 243792855491612387449843)
                  ·
                    rfl

theorem cell20_534133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_534133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534133 prefixEnd_534133 := by exact prefixLift 534133
  have htrace : WordTrace (prefixWord ++ tailWord_534133) baseStart_534133 baseEnd_534133 := by
    simpa [prefixWord, tailWord_534133, baseEnd_534133] using wordTrace_append hprefix tailTrace_534133
  have hstable : (prefixWord ++ tailWord_534133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534133).length < 2 ^ (prefixWord ++ tailWord_534133).sum := by decide
  have hdescent : baseEnd_534133 < baseStart_534133 := by decide
  rcases family_descends (prefixWord ++ tailWord_534133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534137 : List Nat := [1, 2, 1, 3, 3, 1, 3, 4, 2]
def baseStart_534137 : Nat := 118140960795 + 534137 * 2 ^ 59
def prefixEnd_534137 : Nat := 4983230072969 + 3 ^ 40 * 534137 * 2
def baseEnd_534137 : Nat := 243794681200606151316493

theorem tailTrace_534137 : CollatzResearch.WordTrace tailWord_534137 prefixEnd_534137 243794681200606151316493 := by
  unfold tailWord_534137
  simp only [CollatzResearch.WordTrace]
  refine ⟨19481576865920347182048665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12987717910613564788032443 19481576865920347182048665)
  ·
    refine ⟨14611182649440260386536499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19481576865920347182048665 14611182649440260386536499)
    ·
      refine ⟨21916773974160390579804749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14611182649440260386536499 21916773974160390579804749)
      ·
        refine ⟨8218790240310146467426781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21916773974160390579804749 8218790240310146467426781)
        ·
          refine ⟨3082046340116304925285043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8218790240310146467426781 3082046340116304925285043)
          ·
            refine ⟨4623069510174457387927565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3082046340116304925285043 4623069510174457387927565)
            ·
              refine ⟨1733651066315421520472837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4623069510174457387927565 1733651066315421520472837)
              ·
                refine ⟨325059574934141535088657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1733651066315421520472837 325059574934141535088657)
                ·
                  refine ⟨243794681200606151316493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325059574934141535088657 243794681200606151316493)
                  ·
                    rfl

theorem cell20_534137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 2].length) (baseStart_534137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534137 prefixEnd_534137 := by exact prefixLift 534137
  have htrace : WordTrace (prefixWord ++ tailWord_534137) baseStart_534137 baseEnd_534137 := by
    simpa [prefixWord, tailWord_534137, baseEnd_534137] using wordTrace_append hprefix tailTrace_534137
  have hstable : (prefixWord ++ tailWord_534137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534137).length < 2 ^ (prefixWord ++ tailWord_534137).sum := by decide
  have hdescent : baseEnd_534137 < baseStart_534137 := by decide
  rcases family_descends (prefixWord ++ tailWord_534137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534151 : List Nat := [1, 1, 4, 2, 1, 3, 2, 3, 3]
def baseStart_534151 : Nat := 118140960795 + 534151 * 2 ^ 59
def prefixEnd_534151 : Nat := 4983230072969 + 3 ^ 40 * 534151 * 2
def baseEnd_534151 : Nat := 243801071182084324849769

theorem tailTrace_534151 : CollatzResearch.WordTrace tailWord_534151 prefixEnd_534151 243801071182084324849769 := by
  unfold tailWord_534151
  simp only [CollatzResearch.WordTrace]
  refine ⟨19482087487869627573058307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12988058325246418382038871 19482087487869627573058307)
  ·
    refine ⟨29223131231804441359587461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19482087487869627573058307 29223131231804441359587461)
    ·
      refine ⟨5479337105963332754922649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29223131231804441359587461 5479337105963332754922649)
      ·
        refine ⟨4109502829472499566191987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5479337105963332754922649 4109502829472499566191987)
        ·
          refine ⟨6164254244208749349287981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4109502829472499566191987 6164254244208749349287981)
          ·
            refine ⟨2311595341578281005982993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6164254244208749349287981 2311595341578281005982993)
            ·
              refine ⟨1733696506183710754487245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2311595341578281005982993 1733696506183710754487245)
              ·
                refine ⟨650136189818891532932717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1733696506183710754487245 650136189818891532932717)
                ·
                  refine ⟨243801071182084324849769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650136189818891532932717 243801071182084324849769)
                  ·
                    rfl

theorem cell20_534151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 3].length) (baseStart_534151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534151 prefixEnd_534151 := by exact prefixLift 534151
  have htrace : WordTrace (prefixWord ++ tailWord_534151) baseStart_534151 baseEnd_534151 := by
    simpa [prefixWord, tailWord_534151, baseEnd_534151] using wordTrace_append hprefix tailTrace_534151
  have hstable : (prefixWord ++ tailWord_534151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534151).length < 2 ^ (prefixWord ++ tailWord_534151).sum := by decide
  have hdescent : baseEnd_534151 < baseStart_534151 := by decide
  rcases family_descends (prefixWord ++ tailWord_534151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534158 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_534158 : Nat := 118140960795 + 534158 * 2 ^ 59
def prefixEnd_534158 : Nat := 4983230072969 + 3 ^ 40 * 534158 * 2
def baseEnd_534158 : Nat := 243804266172823411616407

theorem tailTrace_534158 : CollatzResearch.WordTrace tailWord_534158 prefixEnd_534158 243804266172823411616407 := by
  unfold tailWord_534158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2435292849855533471070391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12988228532562845179042085 2435292849855533471070391)
  ·
    refine ⟨3652939274783300206605587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2435292849855533471070391 3652939274783300206605587)
    ·
      refine ⟨5479408912174950309908381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3652939274783300206605587 5479408912174950309908381)
      ·
        refine ⟨2054778342065606366215643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5479408912174950309908381 2054778342065606366215643)
        ·
          refine ⟨3082167513098409549323465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2054778342065606366215643 3082167513098409549323465)
          ·
            refine ⟨2311625634823807161992599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3082167513098409549323465 2311625634823807161992599)
            ·
              refine ⟨3467438452235710742988899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2311625634823807161992599 3467438452235710742988899)
              ·
                refine ⟨5201157678353566114483349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3467438452235710742988899 5201157678353566114483349)
                ·
                  refine ⟨243804266172823411616407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5201157678353566114483349 243804266172823411616407)
                  ·
                    rfl

theorem cell20_534158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_534158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534158 prefixEnd_534158 := by exact prefixLift 534158
  have htrace : WordTrace (prefixWord ++ tailWord_534158) baseStart_534158 baseEnd_534158 := by
    simpa [prefixWord, tailWord_534158, baseEnd_534158] using wordTrace_append hprefix tailTrace_534158
  have hstable : (prefixWord ++ tailWord_534158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534158).length < 2 ^ (prefixWord ++ tailWord_534158).sum := by decide
  have hdescent : baseEnd_534158 < baseStart_534158 := by decide
  rcases family_descends (prefixWord ++ tailWord_534158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534179 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 6]
def baseStart_534179 : Nat := 118140960795 + 534179 * 2 ^ 59
def prefixEnd_534179 : Nat := 4983230072969 + 3 ^ 40 * 534179 * 2
def baseEnd_534179 : Nat := 243813851145040671916321

theorem tailTrace_534179 : CollatzResearch.WordTrace tailWord_534179 prefixEnd_534179 243813851145040671916321 := by
  unfold tailWord_534179
  simp only [CollatzResearch.WordTrace]
  refine ⟨19483108731768188355077591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12988739154512125570051727 19483108731768188355077591)
  ·
    refine ⟨29224663097652282532616387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19483108731768188355077591 29224663097652282532616387)
    ·
      refine ⟨43836994646478423798924581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29224663097652282532616387 43836994646478423798924581)
      ·
        refine ⟨8219436496214704462298359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43836994646478423798924581 8219436496214704462298359)
        ·
          refine ⟨12329154744322056693447539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8219436496214704462298359 12329154744322056693447539)
          ·
            refine ⟨18493732116483085040171309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12329154744322056693447539 18493732116483085040171309)
            ·
              refine ⟨6935149543681156890064241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18493732116483085040171309 6935149543681156890064241)
              ·
                refine ⟨5201362157760867667548181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6935149543681156890064241 5201362157760867667548181)
                ·
                  refine ⟨243813851145040671916321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5201362157760867667548181 243813851145040671916321)
                  ·
                    rfl

theorem cell20_534179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_534179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534179 prefixEnd_534179 := by exact prefixLift 534179
  have htrace : WordTrace (prefixWord ++ tailWord_534179) baseStart_534179 baseEnd_534179 := by
    simpa [prefixWord, tailWord_534179, baseEnd_534179] using wordTrace_append hprefix tailTrace_534179
  have hstable : (prefixWord ++ tailWord_534179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534179).length < 2 ^ (prefixWord ++ tailWord_534179).sum := by decide
  have hdescent : baseEnd_534179 < baseStart_534179 := by decide
  rcases family_descends (prefixWord ++ tailWord_534179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534189 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 5]
def baseStart_534189 : Nat := 118140960795 + 534189 * 2 ^ 59
def prefixEnd_534189 : Nat := 4983230072969 + 3 ^ 40 * 534189 * 2
def baseEnd_534189 : Nat := 243818415417525081582947

theorem tailTrace_534189 : CollatzResearch.WordTrace tailWord_534189 prefixEnd_534189 243818415417525081582947 := by
  unfold tailWord_534189
  simp only [CollatzResearch.WordTrace]
  refine ⟨19483473461731960062941621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12988982307821306708627747 19483473461731960062941621)
  ·
    refine ⟨1826575637037371255900777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19483473461731960062941621 1826575637037371255900777)
    ·
      refine ⟨1369931727778028441925583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1826575637037371255900777 1369931727778028441925583)
      ·
        refine ⟨2054897591667042662888375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1369931727778028441925583 2054897591667042662888375)
        ·
          refine ⟨3082346387500563994332563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2054897591667042662888375 3082346387500563994332563)
          ·
            refine ⟨4623519581250845991498845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3082346387500563994332563 4623519581250845991498845)
            ·
              refine ⟨1733819842969067246812067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4623519581250845991498845 1733819842969067246812067)
              ·
                refine ⟨2600729764453600870218101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1733819842969067246812067 2600729764453600870218101)
                ·
                  refine ⟨243818415417525081582947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2600729764453600870218101 243818415417525081582947)
                  ·
                    rfl

theorem cell20_534189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_534189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534189 prefixEnd_534189 := by exact prefixLift 534189
  have htrace : WordTrace (prefixWord ++ tailWord_534189) baseStart_534189 baseEnd_534189 := by
    simpa [prefixWord, tailWord_534189, baseEnd_534189] using wordTrace_append hprefix tailTrace_534189
  have hstable : (prefixWord ++ tailWord_534189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534189).length < 2 ^ (prefixWord ++ tailWord_534189).sum := by decide
  have hdescent : baseEnd_534189 < baseStart_534189 := by decide
  rcases family_descends (prefixWord ++ tailWord_534189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534220 : List Nat := [2, 2, 1, 5, 2, 1, 1, 6]
def baseStart_534220 : Nat := 118140960795 + 534220 * 2 ^ 59
def prefixEnd_534220 : Nat := 4983230072969 + 3 ^ 40 * 534220 * 2
def baseEnd_534220 : Nat := 81277521554075583849829

theorem tailTrace_534220 : CollatzResearch.WordTrace tailWord_534220 prefixEnd_534220 81277521554075583849829 := by
  unfold tailWord_534220
  simp only [CollatzResearch.WordTrace]
  refine ⟨9742302062309826178660057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12989736083079768238213409 9742302062309826178660057)
  ·
    refine ⟨7306726546732369633995043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9742302062309826178660057 7306726546732369633995043)
    ·
      refine ⟨10960089820098554450992565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7306726546732369633995043 10960089820098554450992565)
      ·
        refine ⟨1027508420634239479780553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10960089820098554450992565 1027508420634239479780553)
        ·
          refine ⟨770631315475679609835415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1027508420634239479780553 770631315475679609835415)
          ·
            refine ⟨1155946973213519414753123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770631315475679609835415 1155946973213519414753123)
            ·
              refine ⟨1733920459820279122129685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155946973213519414753123 1733920459820279122129685)
              ·
                refine ⟨81277521554075583849829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1733920459820279122129685 81277521554075583849829)
                ·
                  rfl

theorem cell20_534220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_534220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534220 prefixEnd_534220 := by exact prefixLift 534220
  have htrace : WordTrace (prefixWord ++ tailWord_534220) baseStart_534220 baseEnd_534220 := by
    simpa [prefixWord, tailWord_534220, baseEnd_534220] using wordTrace_append hprefix tailTrace_534220
  have hstable : (prefixWord ++ tailWord_534220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534220).length < 2 ^ (prefixWord ++ tailWord_534220).sum := by decide
  have hdescent : baseEnd_534220 < baseStart_534220 := by decide
  rcases family_descends (prefixWord ++ tailWord_534220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534237 : List Nat := [1, 4, 3, 3, 1, 2, 6]
def baseStart_534237 : Nat := 118140960795 + 534237 * 2 ^ 59
def prefixEnd_534237 : Nat := 4983230072969 + 3 ^ 40 * 534237 * 2
def baseEnd_534237 : Nat := 27093369325050027553639

theorem tailTrace_534237 : CollatzResearch.WordTrace tailWord_534237 prefixEnd_534237 27093369325050027553639 := by
  unfold tailWord_534237
  simp only [CollatzResearch.WordTrace]
  refine ⟨19485224165558064260688965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12990149443705376173792643 19485224165558064260688965)
  ·
    refine ⟨3653479531042137048879181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19485224165558064260688965 3653479531042137048879181)
    ·
      refine ⟨1370054824140801393329693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3653479531042137048879181 1370054824140801393329693)
      ·
        refine ⟨513770559052800522498635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1370054824140801393329693 513770559052800522498635)
        ·
          refine ⟨770655838579200783747953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513770559052800522498635 770655838579200783747953)
          ·
            refine ⟨577991878934400587810965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 770655838579200783747953 577991878934400587810965)
            ·
              refine ⟨27093369325050027553639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 577991878934400587810965 27093369325050027553639)
              ·
                rfl

theorem cell20_534237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 6].length) (baseStart_534237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534237 prefixEnd_534237 := by exact prefixLift 534237
  have htrace : WordTrace (prefixWord ++ tailWord_534237) baseStart_534237 baseEnd_534237 := by
    simpa [prefixWord, tailWord_534237, baseEnd_534237] using wordTrace_append hprefix tailTrace_534237
  have hstable : (prefixWord ++ tailWord_534237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534237).length < 2 ^ (prefixWord ++ tailWord_534237).sum := by decide
  have hdescent : baseEnd_534237 < baseStart_534237 := by decide
  rcases family_descends (prefixWord ++ tailWord_534237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534247 : List Nat := [1, 1, 5, 4, 2, 1, 1, 1, 4]
def baseStart_534247 : Nat := 118140960795 + 534247 * 2 ^ 59
def prefixEnd_534247 : Nat := 4983230072969 + 3 ^ 40 * 534247 * 2
def baseEnd_534247 : Nat := 243844888197934657649377

theorem tailTrace_534247 : CollatzResearch.WordTrace tailWord_534247 prefixEnd_534247 243844888197934657649377 := by
  unfold tailWord_534247
  simp only [CollatzResearch.WordTrace]
  refine ⟨19485588895521835968552995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12990392597014557312368663 19485588895521835968552995)
  ·
    refine ⟨29228383343282753952829493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19485588895521835968552995 29228383343282753952829493)
    ·
      refine ⟨2740160938432758183077765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29228383343282753952829493 2740160938432758183077765)
      ·
        refine ⟨513780175956142159327081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2740160938432758183077765 513780175956142159327081)
        ·
          refine ⟨385335131967106619495311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513780175956142159327081 385335131967106619495311)
          ·
            refine ⟨578002697950659929242967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385335131967106619495311 578002697950659929242967)
            ·
              refine ⟨867004046925989893864451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578002697950659929242967 867004046925989893864451)
              ·
                refine ⟨1300506070388984840796677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867004046925989893864451 1300506070388984840796677)
                ·
                  refine ⟨243844888197934657649377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1300506070388984840796677 243844888197934657649377)
                  ·
                    rfl

theorem cell20_534247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 4].length) (baseStart_534247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534247 prefixEnd_534247 := by exact prefixLift 534247
  have htrace : WordTrace (prefixWord ++ tailWord_534247) baseStart_534247 baseEnd_534247 := by
    simpa [prefixWord, tailWord_534247, baseEnd_534247] using wordTrace_append hprefix tailTrace_534247
  have hstable : (prefixWord ++ tailWord_534247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534247).length < 2 ^ (prefixWord ++ tailWord_534247).sum := by decide
  have hdescent : baseEnd_534247 < baseStart_534247 := by decide
  rcases family_descends (prefixWord ++ tailWord_534247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534286 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_534286 : Nat := 118140960795 + 534286 * 2 ^ 59
def prefixEnd_534286 : Nat := 4983230072969 + 3 ^ 40 * 534286 * 2
def baseEnd_534286 : Nat := 243862688860623855349217

theorem tailTrace_534286 : CollatzResearch.WordTrace tailWord_534286 prefixEnd_534286 243862688860623855349217 := by
  unfold tailWord_534286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2435876417797568203652839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12991340894920363752815141 2435876417797568203652839)
  ·
    refine ⟨3653814626696352305479259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2435876417797568203652839 3653814626696352305479259)
    ·
      refine ⟨5480721940044528458218889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3653814626696352305479259 5480721940044528458218889)
      ·
        refine ⟨4110541455033396343664167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5480721940044528458218889 4110541455033396343664167)
        ·
          refine ⟨6165812182550094515496251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4110541455033396343664167 6165812182550094515496251)
          ·
            refine ⟨9248718273825141773244377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6165812182550094515496251 9248718273825141773244377)
            ·
              refine ⟨6936538705368856329933283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9248718273825141773244377 6936538705368856329933283)
              ·
                refine ⟨10404808058053284494899925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6936538705368856329933283 10404808058053284494899925)
                ·
                  refine ⟨243862688860623855349217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10404808058053284494899925 243862688860623855349217)
                  ·
                    rfl

theorem cell20_534286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_534286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534286 prefixEnd_534286 := by exact prefixLift 534286
  have htrace : WordTrace (prefixWord ++ tailWord_534286) baseStart_534286 baseEnd_534286 := by
    simpa [prefixWord, tailWord_534286, baseEnd_534286] using wordTrace_append hprefix tailTrace_534286
  have hstable : (prefixWord ++ tailWord_534286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534286).length < 2 ^ (prefixWord ++ tailWord_534286).sum := by decide
  have hdescent : baseEnd_534286 < baseStart_534286 := by decide
  rcases family_descends (prefixWord ++ tailWord_534286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534292 : List Nat := [2, 4, 4, 1, 2, 7]
def baseStart_534292 : Nat := 118140960795 + 534292 * 2 ^ 59
def prefixEnd_534292 : Nat := 4983230072969 + 3 ^ 40 * 534292 * 2
def baseEnd_534292 : Nat := 9032052867559796338859

theorem tailTrace_534292 : CollatzResearch.WordTrace tailWord_534292 prefixEnd_534292 9032052867559796338859 := by
  unfold tailWord_534292
  simp only [CollatzResearch.WordTrace]
  refine ⟨9743615090179404326970565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12991486786905872435960753 9743615090179404326970565)
  ·
    refine ⟨1826927829408638311306981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9743615090179404326970565 1826927829408638311306981)
    ·
      refine ⟨342548968014119683370059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1826927829408638311306981 342548968014119683370059)
      ·
        refine ⟨513823452021179525055089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342548968014119683370059 513823452021179525055089)
        ·
          refine ⟨385367589015884643791317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513823452021179525055089 385367589015884643791317)
          ·
            refine ⟨9032052867559796338859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 385367589015884643791317 9032052867559796338859)
            ·
              rfl

theorem cell20_534292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 7].length) (baseStart_534292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534292 prefixEnd_534292 := by exact prefixLift 534292
  have htrace : WordTrace (prefixWord ++ tailWord_534292) baseStart_534292 baseEnd_534292 := by
    simpa [prefixWord, tailWord_534292, baseEnd_534292] using wordTrace_append hprefix tailTrace_534292
  have hstable : (prefixWord ++ tailWord_534292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534292).length < 2 ^ (prefixWord ++ tailWord_534292).sum := by decide
  have hdescent : baseEnd_534292 < baseStart_534292 := by decide
  rcases family_descends (prefixWord ++ tailWord_534292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534302 : List Nat := [4, 3, 2, 2, 1, 1, 1, 4, 2]
def baseStart_534302 : Nat := 118140960795 + 534302 * 2 ^ 59
def prefixEnd_534302 : Nat := 4983230072969 + 3 ^ 40 * 534302 * 2
def baseEnd_534302 : Nat := 243869991696598910815819

theorem tailTrace_534302 : CollatzResearch.WordTrace tailWord_534302 prefixEnd_534302 243869991696598910815819 := by
  unfold tailWord_534302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2435949363790322545225645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12991729940215053574536773 2435949363790322545225645)
  ·
    refine ⟨913481011421370954459617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2435949363790322545225645 913481011421370954459617)
    ·
      refine ⟨685110758566028215844713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 913481011421370954459617 685110758566028215844713)
      ·
        refine ⟨513833068924521161883535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 685110758566028215844713 513833068924521161883535)
        ·
          refine ⟨770749603386781742825303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513833068924521161883535 770749603386781742825303)
          ·
            refine ⟨1156124405080172614237955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770749603386781742825303 1156124405080172614237955)
            ·
              refine ⟨1734186607620258921356933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1156124405080172614237955 1734186607620258921356933)
              ·
                refine ⟨325159988928798547754425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1734186607620258921356933 325159988928798547754425)
                ·
                  refine ⟨243869991696598910815819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325159988928798547754425 243869991696598910815819)
                  ·
                    rfl

theorem cell20_534302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_534302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534302 prefixEnd_534302 := by exact prefixLift 534302
  have htrace : WordTrace (prefixWord ++ tailWord_534302) baseStart_534302 baseEnd_534302 := by
    simpa [prefixWord, tailWord_534302, baseEnd_534302] using wordTrace_append hprefix tailTrace_534302
  have hstable : (prefixWord ++ tailWord_534302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534302).length < 2 ^ (prefixWord ++ tailWord_534302).sum := by decide
  have hdescent : baseEnd_534302 < baseStart_534302 := by decide
  rcases family_descends (prefixWord ++ tailWord_534302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534303 : List Nat := [1, 1, 2, 4, 2, 1, 4, 2, 3]
def baseStart_534303 : Nat := 118140960795 + 534303 * 2 ^ 59
def prefixEnd_534303 : Nat := 4983230072969 + 3 ^ 40 * 534303 * 2
def baseEnd_534303 : Nat := 243870448123847351782481

theorem tailTrace_534303 : CollatzResearch.WordTrace tailWord_534303 prefixEnd_534303 243870448123847351782481 := by
  unfold tailWord_534303
  simp only [CollatzResearch.WordTrace]
  refine ⟨19487631383318957532591563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12991754255545971688394375 19487631383318957532591563)
  ·
    refine ⟨29231447074978436298887345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19487631383318957532591563 29231447074978436298887345)
    ·
      refine ⟨21923585306233827224165509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29231447074978436298887345 21923585306233827224165509)
      ·
        refine ⟨4110672244918842604531033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21923585306233827224165509 4110672244918842604531033)
        ·
          refine ⟨3083004183689131953398275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4110672244918842604531033 3083004183689131953398275)
          ·
            refine ⟨4624506275533697930097413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3083004183689131953398275 4624506275533697930097413)
            ·
              refine ⟨867094926662568361893265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4624506275533697930097413 867094926662568361893265)
              ·
                refine ⟨650321194996926271419949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 867094926662568361893265 650321194996926271419949)
                ·
                  refine ⟨243870448123847351782481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650321194996926271419949 243870448123847351782481)
                  ·
                    rfl

theorem cell20_534303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 3].length) (baseStart_534303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534303 prefixEnd_534303 := by exact prefixLift 534303
  have htrace : WordTrace (prefixWord ++ tailWord_534303) baseStart_534303 baseEnd_534303 := by
    simpa [prefixWord, tailWord_534303, baseEnd_534303] using wordTrace_append hprefix tailTrace_534303
  have hstable : (prefixWord ++ tailWord_534303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534303).length < 2 ^ (prefixWord ++ tailWord_534303).sum := by decide
  have hdescent : baseEnd_534303 < baseStart_534303 := by decide
  rcases family_descends (prefixWord ++ tailWord_534303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534362 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_534362 : Nat := 118140960795 + 534362 * 2 ^ 59
def prefixEnd_534362 : Nat := 4983230072969 + 3 ^ 40 * 534362 * 2
def baseEnd_534362 : Nat := 243897377331505368815573

theorem tailTrace_534362 : CollatzResearch.WordTrace tailWord_534362 prefixEnd_534362 243897377331505368815573 := by
  unfold tailWord_534362
  simp only [CollatzResearch.WordTrace]
  refine ⟨4872445822526302652247335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12993188860070140405992893 4872445822526302652247335)
  ·
    refine ⟨7308668733789453978371003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4872445822526302652247335 7308668733789453978371003)
    ·
      refine ⟨10963003100684180967556505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7308668733789453978371003 10963003100684180967556505)
      ·
        refine ⟨8222252325513135725667379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10963003100684180967556505 8222252325513135725667379)
        ·
          refine ⟨12333378488269703588501069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8222252325513135725667379 12333378488269703588501069)
          ·
            refine ⟨4625016933101138845687901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12333378488269703588501069 4625016933101138845687901)
            ·
              refine ⟨1734381349912927067132963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4625016933101138845687901 1734381349912927067132963)
              ·
                refine ⟨2601572024869390600699445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1734381349912927067132963 2601572024869390600699445)
                ·
                  refine ⟨243897377331505368815573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2601572024869390600699445 243897377331505368815573)
                  ·
                    rfl

theorem cell20_534362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_534362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534362 prefixEnd_534362 := by exact prefixLift 534362
  have htrace : WordTrace (prefixWord ++ tailWord_534362) baseStart_534362 baseEnd_534362 := by
    simpa [prefixWord, tailWord_534362, baseEnd_534362] using wordTrace_append hprefix tailTrace_534362
  have hstable : (prefixWord ++ tailWord_534362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534362).length < 2 ^ (prefixWord ++ tailWord_534362).sum := by decide
  have hdescent : baseEnd_534362 < baseStart_534362 := by decide
  rcases family_descends (prefixWord ++ tailWord_534362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534403 : List Nat := [1, 1, 1, 3, 4, 2, 3, 3, 2]
def baseStart_534403 : Nat := 118140960795 + 534403 * 2 ^ 59
def prefixEnd_534403 : Nat := 4983230072969 + 3 ^ 40 * 534403 * 2
def baseEnd_534403 : Nat := 243916090848691448448739

theorem tailTrace_534403 : CollatzResearch.WordTrace tailWord_534403 prefixEnd_534403 243916090848691448448739 := by
  unfold tailWord_534403
  simp only [CollatzResearch.WordTrace]
  refine ⟨19491278682956674611231863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12994185788637783074154575 19491278682956674611231863)
  ·
    refine ⟨29236918024435011916847795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19491278682956674611231863 29236918024435011916847795)
    ·
      refine ⟨43855377036652517875271693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29236918024435011916847795 43855377036652517875271693)
      ·
        refine ⟨16445766388744694203226885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43855377036652517875271693 16445766388744694203226885)
        ·
          refine ⟨3083581197889630163105041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16445766388744694203226885 3083581197889630163105041)
          ·
            refine ⟨2312685898417222622328781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3083581197889630163105041 2312685898417222622328781)
            ·
              refine ⟨867257211906458483373293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2312685898417222622328781 867257211906458483373293)
              ·
                refine ⟨325221454464921931264985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 867257211906458483373293 325221454464921931264985)
                ·
                  refine ⟨243916090848691448448739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325221454464921931264985 243916090848691448448739)
                  ·
                    rfl

theorem cell20_534403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 2].length) (baseStart_534403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534403 prefixEnd_534403 := by exact prefixLift 534403
  have htrace : WordTrace (prefixWord ++ tailWord_534403) baseStart_534403 baseEnd_534403 := by
    simpa [prefixWord, tailWord_534403, baseEnd_534403] using wordTrace_append hprefix tailTrace_534403
  have hstable : (prefixWord ++ tailWord_534403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534403).length < 2 ^ (prefixWord ++ tailWord_534403).sum := by decide
  have hdescent : baseEnd_534403 < baseStart_534403 := by decide
  rcases family_descends (prefixWord ++ tailWord_534403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534410 : List Nat := [3, 1, 2, 4, 2, 2, 6]
def baseStart_534410 : Nat := 118140960795 + 534410 * 2 ^ 59
def prefixEnd_534410 : Nat := 4983230072969 + 3 ^ 40 * 534410 * 2
def baseEnd_534410 : Nat := 27102142871047837246153

theorem tailTrace_534410 : CollatzResearch.WordTrace tailWord_534410 prefixEnd_534410 27102142871047837246153 := by
  unfold tailWord_534410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4872883498482828701684171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12994355995954209871157789 4872883498482828701684171)
  ·
    refine ⟨7309325247724243052526257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4872883498482828701684171 7309325247724243052526257)
    ·
      refine ⟨5481993935793182289394693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7309325247724243052526257 5481993935793182289394693)
      ·
        refine ⟨1027873862961221679261505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5481993935793182289394693 1027873862961221679261505)
        ·
          refine ⟨770905397220916259446129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1027873862961221679261505 770905397220916259446129)
          ·
            refine ⟨578179047915687194584597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 770905397220916259446129 578179047915687194584597)
            ·
              refine ⟨27102142871047837246153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 578179047915687194584597 27102142871047837246153)
              ·
                rfl

theorem cell20_534410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 6].length) (baseStart_534410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534410 prefixEnd_534410 := by exact prefixLift 534410
  have htrace : WordTrace (prefixWord ++ tailWord_534410) baseStart_534410 baseEnd_534410 := by
    simpa [prefixWord, tailWord_534410, baseEnd_534410] using wordTrace_append hprefix tailTrace_534410
  have hstable : (prefixWord ++ tailWord_534410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534410).length < 2 ^ (prefixWord ++ tailWord_534410).sum := by decide
  have hdescent : baseEnd_534410 < baseStart_534410 := by decide
  rcases family_descends (prefixWord ++ tailWord_534410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534434 : List Nat := [3, 3, 1, 2, 3, 1, 1, 3, 3]
def baseStart_534434 : Nat := 118140960795 + 534434 * 2 ^ 59
def prefixEnd_534434 : Nat := 4983230072969 + 3 ^ 40 * 534434 * 2
def baseEnd_534434 : Nat := 243930240093393118415279

theorem tailTrace_534434 : CollatzResearch.WordTrace tailWord_534434 prefixEnd_534434 243930240093393118415279 := by
  unfold tailWord_534434
  simp only [CollatzResearch.WordTrace]
  refine ⟨4873102336461091726402589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12994939563896244603740237 4873102336461091726402589)
  ·
    refine ⟨1827413376172909397400971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4873102336461091726402589 1827413376172909397400971)
    ·
      refine ⟨2741120064259364096101457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1827413376172909397400971 2741120064259364096101457)
      ·
        refine ⟨2055840048194523072076093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2741120064259364096101457 2055840048194523072076093)
        ·
          refine ⟨770940018072946152028535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2055840048194523072076093 770940018072946152028535)
          ·
            refine ⟨1156410027109419228042803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770940018072946152028535 1156410027109419228042803)
            ·
              refine ⟨1734615040664128842064205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1156410027109419228042803 1734615040664128842064205)
              ·
                refine ⟨650480640249048315774077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1734615040664128842064205 650480640249048315774077)
                ·
                  refine ⟨243930240093393118415279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650480640249048315774077 243930240093393118415279)
                  ·
                    rfl

theorem cell20_534434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_534434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534434 prefixEnd_534434 := by exact prefixLift 534434
  have htrace : WordTrace (prefixWord ++ tailWord_534434) baseStart_534434 baseEnd_534434 := by
    simpa [prefixWord, tailWord_534434, baseEnd_534434] using wordTrace_append hprefix tailTrace_534434
  have hstable : (prefixWord ++ tailWord_534434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534434).length < 2 ^ (prefixWord ++ tailWord_534434).sum := by decide
  have hdescent : baseEnd_534434 < baseStart_534434 := by decide
  rcases family_descends (prefixWord ++ tailWord_534434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534559 : List Nat := [1, 1, 2, 4, 1, 2, 1, 4, 4]
def baseStart_534559 : Nat := 118140960795 + 534559 * 2 ^ 59
def prefixEnd_534559 : Nat := 4983230072969 + 3 ^ 40 * 534559 * 2
def baseEnd_534559 : Nat := 243987293499448239248101

theorem tailTrace_534559 : CollatzResearch.WordTrace tailWord_534559 prefixEnd_534559 243987293499448239248101 := by
  unfold tailWord_534559
  simp only [CollatzResearch.WordTrace]
  refine ⟨19496968470391513253910731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12997978980261008835940487 19496968470391513253910731)
  ·
    refine ⟨29245452705587269880866097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19496968470391513253910731 29245452705587269880866097)
    ·
      refine ⟨21934089529190452410649573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29245452705587269880866097 21934089529190452410649573)
      ·
        refine ⟨4112641786723209826996795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21934089529190452410649573 4112641786723209826996795)
        ·
          refine ⟨6168962680084814740495193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4112641786723209826996795 6168962680084814740495193)
          ·
            refine ⟨4626722010063611055371395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6168962680084814740495193 4626722010063611055371395)
            ·
              refine ⟨6940083015095416583057093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4626722010063611055371395 6940083015095416583057093)
              ·
                refine ⟨1301265565330390609323205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6940083015095416583057093 1301265565330390609323205)
                ·
                  refine ⟨243987293499448239248101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1301265565330390609323205 243987293499448239248101)
                  ·
                    rfl

theorem cell20_534559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_534559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534559 prefixEnd_534559 := by exact prefixLift 534559
  have htrace : WordTrace (prefixWord ++ tailWord_534559) baseStart_534559 baseEnd_534559 := by
    simpa [prefixWord, tailWord_534559, baseEnd_534559] using wordTrace_append hprefix tailTrace_534559
  have hstable : (prefixWord ++ tailWord_534559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534559).length < 2 ^ (prefixWord ++ tailWord_534559).sum := by decide
  have hdescent : baseEnd_534559 < baseStart_534559 := by decide
  rcases family_descends (prefixWord ++ tailWord_534559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534568 : List Nat := [2, 1, 5, 3, 2, 1, 1, 3, 2]
def baseStart_534568 : Nat := 118140960795 + 534568 * 2 ^ 59
def prefixEnd_534568 : Nat := 4983230072969 + 3 ^ 40 * 534568 * 2
def baseEnd_534568 : Nat := 243991401344684207948065

theorem tailTrace_534568 : CollatzResearch.WordTrace tailWord_534568 prefixEnd_534568 243991401344684207948065 := by
  unfold tailWord_534568
  simp only [CollatzResearch.WordTrace]
  refine ⟨9748648363679453895494179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12998197818239271860658905 9748648363679453895494179)
  ·
    refine ⟨14622972545519180843241269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9748648363679453895494179 14622972545519180843241269)
    ·
      refine ⟨1370903676142423204053869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14622972545519180843241269 1370903676142423204053869)
      ·
        refine ⟨514088878553408701520201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1370903676142423204053869 514088878553408701520201)
        ·
          refine ⟨385566658915056526140151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514088878553408701520201 385566658915056526140151)
          ·
            refine ⟨578349988372584789210227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385566658915056526140151 578349988372584789210227)
            ·
              refine ⟨867524982558877183815341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578349988372584789210227 867524982558877183815341)
              ·
                refine ⟨325321868459578943930753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 867524982558877183815341 325321868459578943930753)
                ·
                  refine ⟨243991401344684207948065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325321868459578943930753 243991401344684207948065)
                  ·
                    rfl

theorem cell20_534568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 2].length) (baseStart_534568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534568 prefixEnd_534568 := by exact prefixLift 534568
  have htrace : WordTrace (prefixWord ++ tailWord_534568) baseStart_534568 baseEnd_534568 := by
    simpa [prefixWord, tailWord_534568, baseEnd_534568] using wordTrace_append hprefix tailTrace_534568
  have hstable : (prefixWord ++ tailWord_534568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534568).length < 2 ^ (prefixWord ++ tailWord_534568).sum := by decide
  have hdescent : baseEnd_534568 < baseStart_534568 := by decide
  rcases family_descends (prefixWord ++ tailWord_534568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534593 : List Nat := [1, 2, 5, 1, 2, 3, 1, 1, 4]
def baseStart_534593 : Nat := 118140960795 + 534593 * 2 ^ 59
def prefixEnd_534593 : Nat := 4983230072969 + 3 ^ 40 * 534593 * 2
def baseEnd_534593 : Nat := 244002812025895232114629

theorem tailTrace_534593 : CollatzResearch.WordTrace tailWord_534593 prefixEnd_534593 244002812025895232114629 := by
  unfold tailWord_534593
  simp only [CollatzResearch.WordTrace]
  refine ⟨19498208552268337060648433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12998805701512224707098955 19498208552268337060648433)
  ·
    refine ⟨14623656414201252795486325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19498208552268337060648433 14623656414201252795486325)
    ·
      refine ⟨1370967788831367449576843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14623656414201252795486325 1370967788831367449576843)
      ·
        refine ⟨2056451683247051174365265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1370967788831367449576843 2056451683247051174365265)
        ·
          refine ⟨1542338762435288380773949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2056451683247051174365265 1542338762435288380773949)
          ·
            refine ⟨578377035913233142790231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1542338762435288380773949 578377035913233142790231)
            ·
              refine ⟨867565553869849714185347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578377035913233142790231 867565553869849714185347)
              ·
                refine ⟨1301348330804774571278021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867565553869849714185347 1301348330804774571278021)
                ·
                  refine ⟨244002812025895232114629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1301348330804774571278021 244002812025895232114629)
                  ·
                    rfl

theorem cell20_534593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 4].length) (baseStart_534593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534593 prefixEnd_534593 := by exact prefixLift 534593
  have htrace : WordTrace (prefixWord ++ tailWord_534593) baseStart_534593 baseEnd_534593 := by
    simpa [prefixWord, tailWord_534593, baseEnd_534593] using wordTrace_append hprefix tailTrace_534593
  have hstable : (prefixWord ++ tailWord_534593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534593).length < 2 ^ (prefixWord ++ tailWord_534593).sum := by decide
  have hdescent : baseEnd_534593 < baseStart_534593 := by decide
  rcases family_descends (prefixWord ++ tailWord_534593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534604 : List Nat := [2, 2, 1, 3, 1, 1, 3, 7]
def baseStart_534604 : Nat := 118140960795 + 534604 * 2 ^ 59
def prefixEnd_534604 : Nat := 4983230072969 + 3 ^ 40 * 534604 * 2
def baseEnd_534604 : Nat := 81335944241876027582639

theorem tailTrace_534604 : CollatzResearch.WordTrace tailWord_534604 prefixEnd_534604 81335944241876027582639 := by
  unfold tailWord_534604
  simp only [CollatzResearch.WordTrace]
  refine ⟨9749304877614242969649433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12999073170152323959532577 9749304877614242969649433)
  ·
    refine ⟨7311978658210682227237075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9749304877614242969649433 7311978658210682227237075)
    ·
      refine ⟨10967967987316023340855613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7311978658210682227237075 10967967987316023340855613)
      ·
        refine ⟨4112987995243508752820855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10967967987316023340855613 4112987995243508752820855)
        ·
          refine ⟨6169481992865263129231283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4112987995243508752820855 6169481992865263129231283)
          ·
            refine ⟨9254222989297894693846925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6169481992865263129231283 9254222989297894693846925)
            ·
              refine ⟨3470333620986710510192597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9254222989297894693846925 3470333620986710510192597)
              ·
                refine ⟨81335944241876027582639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3470333620986710510192597 81335944241876027582639)
                ·
                  rfl

theorem cell20_534604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_534604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534604 prefixEnd_534604 := by exact prefixLift 534604
  have htrace : WordTrace (prefixWord ++ tailWord_534604) baseStart_534604 baseEnd_534604 := by
    simpa [prefixWord, tailWord_534604, baseEnd_534604] using wordTrace_append hprefix tailTrace_534604
  have hstable : (prefixWord ++ tailWord_534604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534604).length < 2 ^ (prefixWord ++ tailWord_534604).sum := by decide
  have hdescent : baseEnd_534604 < baseStart_534604 := by decide
  rcases family_descends (prefixWord ++ tailWord_534604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534642 : List Nat := [3, 2, 1, 2, 2, 10]
def baseStart_534642 : Nat := 118140960795 + 534642 * 2 ^ 59
def prefixEnd_534642 : Nat := 4983230072969 + 3 ^ 40 * 534642 * 2
def baseEnd_534642 : Nat := 9037969517076623684485

theorem tailTrace_534642 : CollatzResearch.WordTrace tailWord_534642 prefixEnd_534642 9037969517076623684485 := by
  unfold tailWord_534642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4874998932272704607295545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12999997152727212286121453 4874998932272704607295545)
  ·
    refine ⟨3656249199204528455471659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4874998932272704607295545 3656249199204528455471659)
    ·
      refine ⟨5484373798806792683207489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3656249199204528455471659 5484373798806792683207489)
      ·
        refine ⟨4113280349105094512405617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5484373798806792683207489 4113280349105094512405617)
        ·
          refine ⟨3084960261828820884304213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4113280349105094512405617 3084960261828820884304213)
          ·
            refine ⟨9037969517076623684485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3084960261828820884304213 9037969517076623684485)
            ·
              rfl

theorem cell20_534642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 10].length) (baseStart_534642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534642 prefixEnd_534642 := by exact prefixLift 534642
  have htrace : WordTrace (prefixWord ++ tailWord_534642) baseStart_534642 baseEnd_534642 := by
    simpa [prefixWord, tailWord_534642, baseEnd_534642] using wordTrace_append hprefix tailTrace_534642
  have hstable : (prefixWord ++ tailWord_534642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534642).length < 2 ^ (prefixWord ++ tailWord_534642).sum := by decide
  have hdescent : baseEnd_534642 < baseStart_534642 := by decide
  rcases family_descends (prefixWord ++ tailWord_534642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534659 : List Nat := [1, 1, 1, 3, 3, 5, 1, 5]
def baseStart_534659 : Nat := 118140960795 + 534659 * 2 ^ 59
def prefixEnd_534659 : Nat := 4983230072969 + 3 ^ 40 * 534659 * 2
def baseEnd_534659 : Nat := 81344312074764111971453

theorem tailTrace_534659 : CollatzResearch.WordTrace tailWord_534659 prefixEnd_534659 81344312074764111971453 := by
  unfold tailWord_534659
  simp only [CollatzResearch.WordTrace]
  refine ⟨19500615770029230332551031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13000410513352820221700687 19500615770029230332551031)
  ·
    refine ⟨29250923655043845498826547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19500615770029230332551031 29250923655043845498826547)
    ·
      refine ⟨43876385482565768248239821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29250923655043845498826547 43876385482565768248239821)
      ·
        refine ⟨16453644555962163093089933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43876385482565768248239821 16453644555962163093089933)
        ·
          refine ⟨6170116708485811159908725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16453644555962163093089933 6170116708485811159908725)
          ·
            refine ⟨578448441420544796241443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6170116708485811159908725 578448441420544796241443)
            ·
              refine ⟨867672662130817194362165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578448441420544796241443 867672662130817194362165)
              ·
                refine ⟨81344312074764111971453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 867672662130817194362165 81344312074764111971453)
                ·
                  rfl

theorem cell20_534659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 5].length) (baseStart_534659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534659 prefixEnd_534659 := by exact prefixLift 534659
  have htrace : WordTrace (prefixWord ++ tailWord_534659) baseStart_534659 baseEnd_534659 := by
    simpa [prefixWord, tailWord_534659, baseEnd_534659] using wordTrace_append hprefix tailTrace_534659
  have hstable : (prefixWord ++ tailWord_534659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534659).length < 2 ^ (prefixWord ++ tailWord_534659).sum := by decide
  have hdescent : baseEnd_534659 < baseStart_534659 := by decide
  rcases family_descends (prefixWord ++ tailWord_534659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534711 : List Nat := [1, 1, 3, 1, 4, 2, 1, 3, 4]
def baseStart_534711 : Nat := 118140960795 + 534711 * 2 ^ 59
def prefixEnd_534711 : Nat := 4983230072969 + 3 ^ 40 * 534711 * 2
def baseEnd_534711 : Nat := 244056670441211266180813

theorem tailTrace_534711 : CollatzResearch.WordTrace tailWord_534711 prefixEnd_534711 244056670441211266180813 := by
  unfold tailWord_534711
  simp only [CollatzResearch.WordTrace]
  refine ⟨19502512365840843213443987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13001674910560562142295991 19502512365840843213443987)
  ·
    refine ⟨29253768548761264820165981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19502512365840843213443987 29253768548761264820165981)
    ·
      refine ⟨10970163205785474307562243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29253768548761264820165981 10970163205785474307562243)
      ·
        refine ⟨16455244808678211461343365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10970163205785474307562243 16455244808678211461343365)
        ·
          refine ⟨3085358401627164649001881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16455244808678211461343365 3085358401627164649001881)
          ·
            refine ⟨2314018801220373486751411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3085358401627164649001881 2314018801220373486751411)
            ·
              refine ⟨3471028201830560230127117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2314018801220373486751411 3471028201830560230127117)
              ·
                refine ⟨1301635575686460086297669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3471028201830560230127117 1301635575686460086297669)
                ·
                  refine ⟨244056670441211266180813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1301635575686460086297669 244056670441211266180813)
                  ·
                    rfl

theorem cell20_534711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_534711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534711 prefixEnd_534711 := by exact prefixLift 534711
  have htrace : WordTrace (prefixWord ++ tailWord_534711) baseStart_534711 baseEnd_534711 := by
    simpa [prefixWord, tailWord_534711, baseEnd_534711] using wordTrace_append hprefix tailTrace_534711
  have hstable : (prefixWord ++ tailWord_534711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534711).length < 2 ^ (prefixWord ++ tailWord_534711).sum := by decide
  have hdescent : baseEnd_534711 < baseStart_534711 := by decide
  rcases family_descends (prefixWord ++ tailWord_534711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534741 : List Nat := [1, 3, 2, 4, 3, 1, 1, 3, 2]
def baseStart_534741 : Nat := 118140960795 + 534741 * 2 ^ 59
def prefixEnd_534741 : Nat := 4983230072969 + 3 ^ 40 * 534741 * 2
def baseEnd_534741 : Nat := 244070363258664495180691

theorem tailTrace_534741 : CollatzResearch.WordTrace tailWord_534741 prefixEnd_534741 244070363258664495180691 := by
  unfold tailWord_534741
  simp only [CollatzResearch.WordTrace]
  refine ⟨19503606555732158337036077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13002404370488105558024051 19503606555732158337036077)
  ·
    refine ⟨7313852458399559376388529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19503606555732158337036077 7313852458399559376388529)
    ·
      refine ⟨5485389343799669532291397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7313852458399559376388529 5485389343799669532291397)
      ·
        refine ⟨1028510501962438037304637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5485389343799669532291397 1028510501962438037304637)
        ·
          refine ⟨385691438235914263989239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1028510501962438037304637 385691438235914263989239)
          ·
            refine ⟨578537157353871395983859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385691438235914263989239 578537157353871395983859)
            ·
              refine ⟨867805736030807093975789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578537157353871395983859 867805736030807093975789)
              ·
                refine ⟨325427151011552660240921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 867805736030807093975789 325427151011552660240921)
                ·
                  refine ⟨244070363258664495180691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325427151011552660240921 244070363258664495180691)
                  ·
                    rfl

theorem cell20_534741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_534741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534741 prefixEnd_534741 := by exact prefixLift 534741
  have htrace : WordTrace (prefixWord ++ tailWord_534741) baseStart_534741 baseEnd_534741 := by
    simpa [prefixWord, tailWord_534741, baseEnd_534741] using wordTrace_append hprefix tailTrace_534741
  have hstable : (prefixWord ++ tailWord_534741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534741).length < 2 ^ (prefixWord ++ tailWord_534741).sum := by decide
  have hdescent : baseEnd_534741 < baseStart_534741 := by decide
  rcases family_descends (prefixWord ++ tailWord_534741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534763 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 5]
def baseStart_534763 : Nat := 118140960795 + 534763 * 2 ^ 59
def prefixEnd_534763 : Nat := 4983230072969 + 3 ^ 40 * 534763 * 2
def baseEnd_534763 : Nat := 244080404658130196447267

theorem tailTrace_534763 : CollatzResearch.WordTrace tailWord_534763 prefixEnd_534763 244080404658130196447267 := by
  unfold tailWord_534763
  simp only [CollatzResearch.WordTrace]
  refine ⟨19504408961652456094336943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13002939307768304062891295 19504408961652456094336943)
  ·
    refine ⟨29256613442478684141505415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19504408961652456094336943 29256613442478684141505415)
    ·
      refine ⟨43884920163718026212258123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29256613442478684141505415 43884920163718026212258123)
      ·
        refine ⟨65827380245577039318387185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43884920163718026212258123 65827380245577039318387185)
        ·
          refine ⟨49370535184182779488790389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65827380245577039318387185 49370535184182779488790389)
          ·
            refine ⟨4628487673517135577074099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49370535184182779488790389 4628487673517135577074099)
            ·
              refine ⟨6942731510275703365611149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4628487673517135577074099 6942731510275703365611149)
              ·
                refine ⟨2603524316353388762104181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6942731510275703365611149 2603524316353388762104181)
                ·
                  refine ⟨244080404658130196447267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2603524316353388762104181 244080404658130196447267)
                  ·
                    rfl

theorem cell20_534763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_534763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534763 prefixEnd_534763 := by exact prefixLift 534763
  have htrace : WordTrace (prefixWord ++ tailWord_534763) baseStart_534763 baseEnd_534763 := by
    simpa [prefixWord, tailWord_534763, baseEnd_534763] using wordTrace_append hprefix tailTrace_534763
  have hstable : (prefixWord ++ tailWord_534763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534763).length < 2 ^ (prefixWord ++ tailWord_534763).sum := by decide
  have hdescent : baseEnd_534763 < baseStart_534763 := by decide
  rcases family_descends (prefixWord ++ tailWord_534763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534794 : List Nat := [3, 1, 2, 2, 1, 1, 4, 6]
def baseStart_534794 : Nat := 118140960795 + 534794 * 2 ^ 59
def prefixEnd_534794 : Nat := 4983230072969 + 3 ^ 40 * 534794 * 2
def baseEnd_534794 : Nat := 81364851300943955471269

theorem tailTrace_534794 : CollatzResearch.WordTrace tailWord_534794 prefixEnd_534794 81364851300943955471269 := by
  unfold tailWord_534794
  simp only [CollatzResearch.WordTrace]
  refine ⟨4876384906135037097178859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13003693083026765592476957 4876384906135037097178859)
  ·
    refine ⟨7314577359202555645768289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4876384906135037097178859 7314577359202555645768289)
    ·
      refine ⟨5485933019401916734326217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7314577359202555645768289 5485933019401916734326217)
      ·
        refine ⟨4114449764551437550744663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5485933019401916734326217 4114449764551437550744663)
        ·
          refine ⟨6171674646827156326116995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4114449764551437550744663 6171674646827156326116995)
          ·
            refine ⟨9257511970240734489175493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6171674646827156326116995 9257511970240734489175493)
            ·
              refine ⟨1735783494420137716720405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9257511970240734489175493 1735783494420137716720405)
              ·
                refine ⟨81364851300943955471269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1735783494420137716720405 81364851300943955471269)
                ·
                  rfl

theorem cell20_534794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_534794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534794 prefixEnd_534794 := by exact prefixLift 534794
  have htrace : WordTrace (prefixWord ++ tailWord_534794) baseStart_534794 baseEnd_534794 := by
    simpa [prefixWord, tailWord_534794, baseEnd_534794] using wordTrace_append hprefix tailTrace_534794
  have hstable : (prefixWord ++ tailWord_534794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534794).length < 2 ^ (prefixWord ++ tailWord_534794).sum := by decide
  have hdescent : baseEnd_534794 < baseStart_534794 := by decide
  rcases family_descends (prefixWord ++ tailWord_534794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534814 : List Nat := [4, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_534814 : Nat := 118140960795 + 534814 * 2 ^ 59
def prefixEnd_534814 : Nat := 4983230072969 + 3 ^ 40 * 534814 * 2
def baseEnd_534814 : Nat := 244103682447800685747059

theorem tailTrace_534814 : CollatzResearch.WordTrace tailWord_534814 prefixEnd_534814 244103682447800685747059 := by
  unfold tailWord_534814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2438283635558461475555437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13004179389645127869628997 2438283635558461475555437)
  ·
    refine ⟨914356363334423053333289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2438283635558461475555437 914356363334423053333289)
    ·
      refine ⟨685767272500817289999967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 914356363334423053333289 685767272500817289999967)
      ·
        refine ⟨1028650908751225934999951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685767272500817289999967 1028650908751225934999951)
        ·
          refine ⟨1542976363126838902499927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028650908751225934999951 1542976363126838902499927)
          ·
            refine ⟨2314464544690258353749891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1542976363126838902499927 2314464544690258353749891)
            ·
              refine ⟨3471696817035387530624837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2314464544690258353749891 3471696817035387530624837)
              ·
                refine ⟨650943153194135161992157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3471696817035387530624837 650943153194135161992157)
                ·
                  refine ⟨244103682447800685747059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650943153194135161992157 244103682447800685747059)
                  ·
                    rfl

theorem cell20_534814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_534814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534814 prefixEnd_534814 := by exact prefixLift 534814
  have htrace : WordTrace (prefixWord ++ tailWord_534814) baseStart_534814 baseEnd_534814 := by
    simpa [prefixWord, tailWord_534814, baseEnd_534814] using wordTrace_append hprefix tailTrace_534814
  have hstable : (prefixWord ++ tailWord_534814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534814).length < 2 ^ (prefixWord ++ tailWord_534814).sum := by decide
  have hdescent : baseEnd_534814 < baseStart_534814 := by decide
  rcases family_descends (prefixWord ++ tailWord_534814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534821 : List Nat := [1, 3, 1, 2, 5, 1, 1, 4, 2]
def baseStart_534821 : Nat := 118140960795 + 534821 * 2 ^ 59
def prefixEnd_534821 : Nat := 4983230072969 + 3 ^ 40 * 534821 * 2
def baseEnd_534821 : Nat := 244106877438539772513697

theorem tailTrace_534821 : CollatzResearch.WordTrace tailWord_534821 prefixEnd_534821 244106877438539772513697 := by
  unfold tailWord_534821
  simp only [CollatzResearch.WordTrace]
  refine ⟨19506524395442331999948317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13004349596961554666632211 19506524395442331999948317)
  ·
    refine ⟨7314946648290874499980619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19506524395442331999948317 7314946648290874499980619)
    ·
      refine ⟨10972419972436311749970929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7314946648290874499980619 10972419972436311749970929)
      ·
        refine ⟨8229314979327233812478197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10972419972436311749970929 8229314979327233812478197)
        ·
          refine ⟨771498279311928169919831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8229314979327233812478197 771498279311928169919831)
          ·
            refine ⟨1157247418967892254879747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771498279311928169919831 1157247418967892254879747)
            ·
              refine ⟨1735871128451838382319621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1157247418967892254879747 1735871128451838382319621)
              ·
                refine ⟨325475836584719696684929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1735871128451838382319621 325475836584719696684929)
                ·
                  refine ⟨244106877438539772513697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325475836584719696684929 244106877438539772513697)
                  ·
                    rfl

theorem cell20_534821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_534821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534821 prefixEnd_534821 := by exact prefixLift 534821
  have htrace : WordTrace (prefixWord ++ tailWord_534821) baseStart_534821 baseEnd_534821 := by
    simpa [prefixWord, tailWord_534821, baseEnd_534821] using wordTrace_append hprefix tailTrace_534821
  have hstable : (prefixWord ++ tailWord_534821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534821).length < 2 ^ (prefixWord ++ tailWord_534821).sum := by decide
  have hdescent : baseEnd_534821 < baseStart_534821 := by decide
  rcases family_descends (prefixWord ++ tailWord_534821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534880 : List Nat := [2, 1, 1, 3, 5, 1, 2, 1, 4]
def baseStart_534880 : Nat := 118140960795 + 534880 * 2 ^ 59
def prefixEnd_534880 : Nat := 4983230072969 + 3 ^ 40 * 534880 * 2
def baseEnd_534880 : Nat := 244133806646197789546789

theorem tailTrace_534880 : CollatzResearch.WordTrace tailWord_534880 prefixEnd_534880 244133806646197789546789 := by
  unfold tailWord_534880
  simp only [CollatzResearch.WordTrace]
  refine ⟨9754338151114292538173047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13005784201485723384230729 9754338151114292538173047)
  ·
    refine ⟨14631507226671438807259571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9754338151114292538173047 14631507226671438807259571)
    ·
      refine ⟨21947260840007158210889357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14631507226671438807259571 21947260840007158210889357)
      ·
        refine ⟨8230222815002684329083509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21947260840007158210889357 8230222815002684329083509)
        ·
          refine ⟨771583388906501655851579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8230222815002684329083509 771583388906501655851579)
          ·
            refine ⟨1157375083359752483777369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771583388906501655851579 1157375083359752483777369)
            ·
              refine ⟨868031312519814362833027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1157375083359752483777369 868031312519814362833027)
              ·
                refine ⟨1302046968779721544249541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868031312519814362833027 1302046968779721544249541)
                ·
                  refine ⟨244133806646197789546789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1302046968779721544249541 244133806646197789546789)
                  ·
                    rfl

theorem cell20_534880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_534880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534880 prefixEnd_534880 := by exact prefixLift 534880
  have htrace : WordTrace (prefixWord ++ tailWord_534880) baseStart_534880 baseEnd_534880 := by
    simpa [prefixWord, tailWord_534880, baseEnd_534880] using wordTrace_append hprefix tailTrace_534880
  have hstable : (prefixWord ++ tailWord_534880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534880).length < 2 ^ (prefixWord ++ tailWord_534880).sum := by decide
  have hdescent : baseEnd_534880 < baseStart_534880 := by decide
  rcases family_descends (prefixWord ++ tailWord_534880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534890 : List Nat := [3, 1, 3, 3, 1, 2, 3, 1, 3]
def baseStart_534890 : Nat := 118140960795 + 534890 * 2 ^ 59
def prefixEnd_534890 : Nat := 4983230072969 + 3 ^ 40 * 534890 * 2
def baseEnd_534890 : Nat := 244138370918682199213415

theorem tailTrace_534890 : CollatzResearch.WordTrace tailWord_534890 prefixEnd_534890 244138370918682199213415 := by
  unfold tailWord_534890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4877260258048089196052531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13006027354794904522806749 4877260258048089196052531)
  ·
    refine ⟨7315890387072133794078797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4877260258048089196052531 7315890387072133794078797)
    ·
      refine ⟨2743458895152050172779549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7315890387072133794078797 2743458895152050172779549)
      ·
        refine ⟨1028797085682018814792331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2743458895152050172779549 1028797085682018814792331)
        ·
          refine ⟨1543195628523028222188497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028797085682018814792331 1543195628523028222188497)
          ·
            refine ⟨1157396721392271166641373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1543195628523028222188497 1157396721392271166641373)
            ·
              refine ⟨434023770522101687490515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1157396721392271166641373 434023770522101687490515)
              ·
                refine ⟨651035655783152531235773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434023770522101687490515 651035655783152531235773)
                ·
                  refine ⟨244138370918682199213415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651035655783152531235773 244138370918682199213415)
                  ·
                    rfl

theorem cell20_534890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_534890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534890 prefixEnd_534890 := by exact prefixLift 534890
  have htrace : WordTrace (prefixWord ++ tailWord_534890) baseStart_534890 baseEnd_534890 := by
    simpa [prefixWord, tailWord_534890, baseEnd_534890] using wordTrace_append hprefix tailTrace_534890
  have hstable : (prefixWord ++ tailWord_534890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534890).length < 2 ^ (prefixWord ++ tailWord_534890).sum := by decide
  have hdescent : baseEnd_534890 < baseStart_534890 := by decide
  rcases family_descends (prefixWord ++ tailWord_534890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534942 : List Nat := [4, 3, 1, 2, 1, 2, 2, 5]
def baseStart_534942 : Nat := 118140960795 + 534942 * 2 ^ 59
def prefixEnd_534942 : Nat := 4983230072969 + 3 ^ 40 * 534942 * 2
def baseEnd_534942 : Nat := 81387368378533709826623

theorem tailTrace_534942 : CollatzResearch.WordTrace tailWord_534942 prefixEnd_534942 81387368378533709826623 := by
  unfold tailWord_534942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2438867203500496208137885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13007291752002646443402053 2438867203500496208137885)
  ·
    refine ⟨914575201312686078051707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2438867203500496208137885 914575201312686078051707)
    ·
      refine ⟨1371862801969029117077561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 914575201312686078051707 1371862801969029117077561)
      ·
        refine ⟨1028897101476771837808171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1371862801969029117077561 1028897101476771837808171)
        ·
          refine ⟨1543345652215157756712257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028897101476771837808171 1543345652215157756712257)
          ·
            refine ⟨1157509239161368317534193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1543345652215157756712257 1157509239161368317534193)
            ·
              refine ⟨868131929371026238150645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1157509239161368317534193 868131929371026238150645)
              ·
                refine ⟨81387368378533709826623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 868131929371026238150645 81387368378533709826623)
                ·
                  rfl

theorem cell20_534942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_534942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534942 prefixEnd_534942 := by exact prefixLift 534942
  have htrace : WordTrace (prefixWord ++ tailWord_534942) baseStart_534942 baseEnd_534942 := by
    simpa [prefixWord, tailWord_534942, baseEnd_534942] using wordTrace_append hprefix tailTrace_534942
  have hstable : (prefixWord ++ tailWord_534942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534942).length < 2 ^ (prefixWord ++ tailWord_534942).sum := by decide
  have hdescent : baseEnd_534942 < baseStart_534942 := by decide
  rcases family_descends (prefixWord ++ tailWord_534942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534945 : List Nat := [1, 2, 3, 5, 1, 2, 2, 1, 3]
def baseStart_534945 : Nat := 118140960795 + 534945 * 2 ^ 59
def prefixEnd_534945 : Nat := 4983230072969 + 3 ^ 40 * 534945 * 2
def baseEnd_534945 : Nat := 244163474417346452379857

theorem tailTrace_534945 : CollatzResearch.WordTrace tailWord_534945 prefixEnd_534945 244163474417346452379857 := by
  unfold tailWord_534945
  simp only [CollatzResearch.WordTrace]
  refine ⟨19511047046993101177462289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13007364697995400784974859 19511047046993101177462289)
  ·
    refine ⟨14633285285244825883096717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19511047046993101177462289 14633285285244825883096717)
    ·
      refine ⟨5487481981966809706161269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14633285285244825883096717 5487481981966809706161269)
      ·
        refine ⟨514451435809388409952619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5487481981966809706161269 514451435809388409952619)
        ·
          refine ⟨771677153714082614928929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514451435809388409952619 771677153714082614928929)
          ·
            refine ⟨578757865285561961196697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 771677153714082614928929 578757865285561961196697)
            ·
              refine ⟨434068398964171470897523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578757865285561961196697 434068398964171470897523)
              ·
                refine ⟨651102598446257206346285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434068398964171470897523 651102598446257206346285)
                ·
                  refine ⟨244163474417346452379857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651102598446257206346285 244163474417346452379857)
                  ·
                    rfl

theorem cell20_534945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 3].length) (baseStart_534945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_534945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_534945 prefixEnd_534945 := by exact prefixLift 534945
  have htrace : WordTrace (prefixWord ++ tailWord_534945) baseStart_534945 baseEnd_534945 := by
    simpa [prefixWord, tailWord_534945, baseEnd_534945] using wordTrace_append hprefix tailTrace_534945
  have hstable : (prefixWord ++ tailWord_534945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534945).length < 2 ^ (prefixWord ++ tailWord_534945).sum := by decide
  have hdescent : baseEnd_534945 < baseStart_534945 := by decide
  rcases family_descends (prefixWord ++ tailWord_534945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535015 : List Nat := [1, 1, 5, 2, 1, 1, 3, 2, 4]
def baseStart_535015 : Nat := 118140960795 + 535015 * 2 ^ 59
def prefixEnd_535015 : Nat := 4983230072969 + 3 ^ 40 * 535015 * 2
def baseEnd_535015 : Nat := 244195424324737320046237

theorem tailTrace_535015 : CollatzResearch.WordTrace tailWord_535015 prefixEnd_535015 244195424324737320046237 := by
  unfold tailWord_535015
  simp only [CollatzResearch.WordTrace]
  refine ⟨19513600156739503132510499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13009066771159668755006999 19513600156739503132510499)
  ·
    refine ⟨29270400235109254698765749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19513600156739503132510499 29270400235109254698765749)
    ·
      refine ⟨2744100022041492628009289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29270400235109254698765749 2744100022041492628009289)
      ·
        refine ⟨2058075016531119471006967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2744100022041492628009289 2058075016531119471006967)
        ·
          refine ⟨3087112524796679206510451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058075016531119471006967 3087112524796679206510451)
          ·
            refine ⟨4630668787195018809765677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3087112524796679206510451 4630668787195018809765677)
            ·
              refine ⟨1736500795198132053662129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4630668787195018809765677 1736500795198132053662129)
              ·
                refine ⟨1302375596398599040246597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1736500795198132053662129 1302375596398599040246597)
                ·
                  refine ⟨244195424324737320046237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1302375596398599040246597 244195424324737320046237)
                  ·
                    rfl

theorem cell20_535015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_535015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535015 prefixEnd_535015 := by exact prefixLift 535015
  have htrace : WordTrace (prefixWord ++ tailWord_535015) baseStart_535015 baseEnd_535015 := by
    simpa [prefixWord, tailWord_535015, baseEnd_535015] using wordTrace_append hprefix tailTrace_535015
  have hstable : (prefixWord ++ tailWord_535015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535015).length < 2 ^ (prefixWord ++ tailWord_535015).sum := by decide
  have hdescent : baseEnd_535015 < baseStart_535015 := by decide
  rcases family_descends (prefixWord ++ tailWord_535015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535032 : List Nat := [2, 1, 2, 1, 1, 4, 4, 3, 2]
def baseStart_535032 : Nat := 118140960795 + 535032 * 2 ^ 59
def prefixEnd_535032 : Nat := 4983230072969 + 3 ^ 40 * 535032 * 2
def baseEnd_535032 : Nat := 244203183587960816479501

theorem tailTrace_535032 : CollatzResearch.WordTrace tailWord_535032 prefixEnd_535032 244203183587960816479501 := by
  unfold tailWord_535032
  simp only [CollatzResearch.WordTrace]
  refine ⟨9757110098838957517939675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13009480131785276690586233 9757110098838957517939675)
  ·
    refine ⟨14635665148258436276909513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9757110098838957517939675 14635665148258436276909513)
    ·
      refine ⟨10976748861193827207682135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14635665148258436276909513 10976748861193827207682135)
      ·
        refine ⟨16465123291790740811523203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10976748861193827207682135 16465123291790740811523203)
        ·
          refine ⟨24697684937686111217284805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16465123291790740811523203 24697684937686111217284805)
          ·
            refine ⟨4630815925816145853240901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24697684937686111217284805 4630815925816145853240901)
            ·
              refine ⟨868277986090527347482669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4630815925816145853240901 868277986090527347482669)
              ·
                refine ⟨325604244783947755306001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 868277986090527347482669 325604244783947755306001)
                ·
                  refine ⟨244203183587960816479501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325604244783947755306001 244203183587960816479501)
                  ·
                    rfl

theorem cell20_535032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 2].length) (baseStart_535032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535032 prefixEnd_535032 := by exact prefixLift 535032
  have htrace : WordTrace (prefixWord ++ tailWord_535032) baseStart_535032 baseEnd_535032 := by
    simpa [prefixWord, tailWord_535032, baseEnd_535032] using wordTrace_append hprefix tailTrace_535032
  have hstable : (prefixWord ++ tailWord_535032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535032).length < 2 ^ (prefixWord ++ tailWord_535032).sum := by decide
  have hdescent : baseEnd_535032 < baseStart_535032 := by decide
  rcases family_descends (prefixWord ++ tailWord_535032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535036 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 8]
def baseStart_535036 : Nat := 118140960795 + 535036 * 2 ^ 59
def prefixEnd_535036 : Nat := 4983230072969 + 3 ^ 40 * 535036 * 2
def baseEnd_535036 : Nat := 244205009296954580346151

theorem tailTrace_535036 : CollatzResearch.WordTrace tailWord_535036 prefixEnd_535036 244205009296954580346151 := by
  unfold tailWord_535036
  simp only [CollatzResearch.WordTrace]
  refine ⟨9757183044831711859512481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13009577393108949146016641 9757183044831711859512481)
  ·
    refine ⟨7317887283623783894634361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9757183044831711859512481 7317887283623783894634361)
    ·
      refine ⟨5488415462717837920975771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7317887283623783894634361 5488415462717837920975771)
      ·
        refine ⟨8232623194076756881463657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5488415462717837920975771 8232623194076756881463657)
        ·
          refine ⟨6174467395557567661097743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8232623194076756881463657 6174467395557567661097743)
          ·
            refine ⟨9261701093336351491646615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6174467395557567661097743 9261701093336351491646615)
            ·
              refine ⟨13892551640004527237469923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9261701093336351491646615 13892551640004527237469923)
              ·
                refine ⟨20838827460006790856204885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13892551640004527237469923 20838827460006790856204885)
                ·
                  refine ⟨244205009296954580346151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20838827460006790856204885 244205009296954580346151)
                  ·
                    rfl

theorem cell20_535036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_535036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535036 prefixEnd_535036 := by exact prefixLift 535036
  have htrace : WordTrace (prefixWord ++ tailWord_535036) baseStart_535036 baseEnd_535036 := by
    simpa [prefixWord, tailWord_535036, baseEnd_535036] using wordTrace_append hprefix tailTrace_535036
  have hstable : (prefixWord ++ tailWord_535036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535036).length < 2 ^ (prefixWord ++ tailWord_535036).sum := by decide
  have hdescent : baseEnd_535036 < baseStart_535036 := by decide
  rcases family_descends (prefixWord ++ tailWord_535036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535043 : List Nat := [1, 1, 1, 3, 2, 1, 11]
def baseStart_535043 : Nat := 118140960795 + 535043 * 2 ^ 59
def prefixEnd_535043 : Nat := 4983230072969 + 3 ^ 40 * 535043 * 2
def baseEnd_535043 : Nat := 27134244920854851901421

theorem tailTrace_535043 : CollatzResearch.WordTrace tailWord_535043 prefixEnd_535043 27134244920854851901421 := by
  unfold tailWord_535043
  simp only [CollatzResearch.WordTrace]
  refine ⟨19514621400638063914529783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13009747600425375943019855 19514621400638063914529783)
  ·
    refine ⟨29271932100957095871794675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19514621400638063914529783 29271932100957095871794675)
    ·
      refine ⟨43907898151435643807692013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29271932100957095871794675 43907898151435643807692013)
      ·
        refine ⟨16465461806788366427884505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43907898151435643807692013 16465461806788366427884505)
        ·
          refine ⟨12349096355091274820913379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16465461806788366427884505 12349096355091274820913379)
          ·
            refine ⟨18523644532636912231370069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12349096355091274820913379 18523644532636912231370069)
            ·
              refine ⟨27134244920854851901421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18523644532636912231370069 27134244920854851901421)
              ·
                rfl

theorem cell20_535043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 11].length) (baseStart_535043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535043 prefixEnd_535043 := by exact prefixLift 535043
  have htrace : WordTrace (prefixWord ++ tailWord_535043) baseStart_535043 baseEnd_535043 := by
    simpa [prefixWord, tailWord_535043, baseEnd_535043] using wordTrace_append hprefix tailTrace_535043
  have hstable : (prefixWord ++ tailWord_535043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535043).length < 2 ^ (prefixWord ++ tailWord_535043).sum := by decide
  have hdescent : baseEnd_535043 < baseStart_535043 := by decide
  rcases family_descends (prefixWord ++ tailWord_535043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535098 : List Nat := [3, 1, 1, 1, 3, 5, 6]
def baseStart_535098 : Nat := 118140960795 + 535098 * 2 ^ 59
def prefixEnd_535098 : Nat := 4983230072969 + 3 ^ 40 * 535098 * 2
def baseEnd_535098 : Nat := 27137034198484213364359

theorem tailTrace_535098 : CollatzResearch.WordTrace tailWord_535098 prefixEnd_535098 27137034198484213364359 := by
  unfold tailWord_535098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4879156853859702076945487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13011084943625872205187965 4879156853859702076945487)
  ·
    refine ⟨7318735280789553115418231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4879156853859702076945487 7318735280789553115418231)
    ·
      refine ⟨10978102921184329673127347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7318735280789553115418231 10978102921184329673127347)
      ·
        refine ⟨16467154381776494509691021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10978102921184329673127347 16467154381776494509691021)
        ·
          refine ⟨6175182893166185441134133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16467154381776494509691021 6175182893166185441134133)
          ·
            refine ⟨578923396234329885106325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6175182893166185441134133 578923396234329885106325)
            ·
              refine ⟨27137034198484213364359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 578923396234329885106325 27137034198484213364359)
              ·
                rfl

theorem cell20_535098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 6].length) (baseStart_535098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535098 prefixEnd_535098 := by exact prefixLift 535098
  have htrace : WordTrace (prefixWord ++ tailWord_535098) baseStart_535098 baseEnd_535098 := by
    simpa [prefixWord, tailWord_535098, baseEnd_535098] using wordTrace_append hprefix tailTrace_535098
  have hstable : (prefixWord ++ tailWord_535098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535098).length < 2 ^ (prefixWord ++ tailWord_535098).sum := by decide
  have hdescent : baseEnd_535098 < baseStart_535098 := by decide
  rcases family_descends (prefixWord ++ tailWord_535098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535119 : List Nat := [1, 1, 2, 1, 1, 2, 5, 7]
def baseStart_535119 : Nat := 118140960795 + 535119 * 2 ^ 59
def prefixEnd_535119 : Nat := 4983230072969 + 3 ^ 40 * 535119 * 2
def baseEnd_535119 : Nat := 81414297586191726859715

theorem tailTrace_535119 : CollatzResearch.WordTrace tailWord_535119 prefixEnd_535119 81414297586191726859715 := by
  unfold tailWord_535119
  simp only [CollatzResearch.WordTrace]
  refine ⟨19517393348362728894296411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13011595565575152596197607 19517393348362728894296411)
  ·
    refine ⟨29276090022544093341444617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19517393348362728894296411 29276090022544093341444617)
    ·
      refine ⟨21957067516908070006083463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29276090022544093341444617 21957067516908070006083463)
      ·
        refine ⟨32935601275362105009125195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21957067516908070006083463 32935601275362105009125195)
        ·
          refine ⟨49403401913043157513687793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32935601275362105009125195 49403401913043157513687793)
          ·
            refine ⟨37052551434782368135265845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49403401913043157513687793 37052551434782368135265845)
            ·
              refine ⟨3473676697010847012681173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37052551434782368135265845 3473676697010847012681173)
              ·
                refine ⟨81414297586191726859715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3473676697010847012681173 81414297586191726859715)
                ·
                  rfl

theorem cell20_535119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 7].length) (baseStart_535119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535119 prefixEnd_535119 := by exact prefixLift 535119
  have htrace : WordTrace (prefixWord ++ tailWord_535119) baseStart_535119 baseEnd_535119 := by
    simpa [prefixWord, tailWord_535119, baseEnd_535119] using wordTrace_append hprefix tailTrace_535119
  have hstable : (prefixWord ++ tailWord_535119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535119).length < 2 ^ (prefixWord ++ tailWord_535119).sum := by decide
  have hdescent : baseEnd_535119 < baseStart_535119 := by decide
  rcases family_descends (prefixWord ++ tailWord_535119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535122 : List Nat := [3, 2, 2, 1, 2, 1, 3, 3, 3]
def baseStart_535122 : Nat := 118140960795 + 535122 * 2 ^ 59
def prefixEnd_535122 : Nat := 4983230072969 + 3 ^ 40 * 535122 * 2
def baseEnd_535122 : Nat := 244244262040320503479133

theorem tailTrace_535122 : CollatzResearch.WordTrace tailWord_535122 prefixEnd_535122 244244262040320503479133 := by
  unfold tailWord_535122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4879375691837965101663905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13011668511567906937770413 4879375691837965101663905)
  ·
    refine ⟨3659531768878473826247929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4879375691837965101663905 3659531768878473826247929)
    ·
      refine ⟨2744648826658855369685947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3659531768878473826247929 2744648826658855369685947)
      ·
        refine ⟨4116973239988283054528921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2744648826658855369685947 4116973239988283054528921)
        ·
          refine ⟨3087729929991212290896691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4116973239988283054528921 3087729929991212290896691)
          ·
            refine ⟨4631594894986818436345037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3087729929991212290896691 4631594894986818436345037)
            ·
              refine ⟨1736848085620056913629389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4631594894986818436345037 1736848085620056913629389)
              ·
                refine ⟨651318032107521342611021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1736848085620056913629389 651318032107521342611021)
                ·
                  refine ⟨244244262040320503479133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651318032107521342611021 244244262040320503479133)
                  ·
                    rfl

theorem cell20_535122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_535122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535122 prefixEnd_535122 := by exact prefixLift 535122
  have htrace : WordTrace (prefixWord ++ tailWord_535122) baseStart_535122 baseEnd_535122 := by
    simpa [prefixWord, tailWord_535122, baseEnd_535122] using wordTrace_append hprefix tailTrace_535122
  have hstable : (prefixWord ++ tailWord_535122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535122).length < 2 ^ (prefixWord ++ tailWord_535122).sum := by decide
  have hdescent : baseEnd_535122 < baseStart_535122 := by decide
  rcases family_descends (prefixWord ++ tailWord_535122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535146 : List Nat := [3, 1, 3, 2, 1, 1, 2, 5, 2]
def baseStart_535146 : Nat := 118140960795 + 535146 * 2 ^ 59
def prefixEnd_535146 : Nat := 4983230072969 + 3 ^ 40 * 535146 * 2
def baseEnd_535146 : Nat := 244255216294283086679035

theorem tailTrace_535146 : CollatzResearch.WordTrace tailWord_535146 prefixEnd_535146 244255216294283086679035 := by
  unfold tailWord_535146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4879594529816228126382323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13012252079509941670352861 4879594529816228126382323)
  ·
    refine ⟨7319391794724342189573485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4879594529816228126382323 7319391794724342189573485)
    ·
      refine ⟨2744771923021628321090057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7319391794724342189573485 2744771923021628321090057)
      ·
        refine ⟨2058578942266221240817543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2744771923021628321090057 2058578942266221240817543)
        ·
          refine ⟨3087868413399331861226315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058578942266221240817543 3087868413399331861226315)
          ·
            refine ⟨4631802620098997791839473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3087868413399331861226315 4631802620098997791839473)
            ·
              refine ⟨3473851965074248343879605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4631802620098997791839473 3473851965074248343879605)
              ·
                refine ⟨325673621725710782238713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3473851965074248343879605 325673621725710782238713)
                ·
                  refine ⟨244255216294283086679035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325673621725710782238713 244255216294283086679035)
                  ·
                    rfl

theorem cell20_535146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_535146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535146 prefixEnd_535146 := by exact prefixLift 535146
  have htrace : WordTrace (prefixWord ++ tailWord_535146) baseStart_535146 baseEnd_535146 := by
    simpa [prefixWord, tailWord_535146, baseEnd_535146] using wordTrace_append hprefix tailTrace_535146
  have hstable : (prefixWord ++ tailWord_535146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535146).length < 2 ^ (prefixWord ++ tailWord_535146).sum := by decide
  have hdescent : baseEnd_535146 < baseStart_535146 := by decide
  rcases family_descends (prefixWord ++ tailWord_535146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535198 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_535198 : Nat := 118140960795 + 535198 * 2 ^ 59
def prefixEnd_535198 : Nat := 4983230072969 + 3 ^ 40 * 535198 * 2
def baseEnd_535198 : Nat := 244278950511202016945489

theorem tailTrace_535198 : CollatzResearch.WordTrace tailWord_535198 prefixEnd_535198 244278950511202016945489 := by
  unfold tailWord_535198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2440034339384565673302781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13013516476717683590948165 2440034339384565673302781)
  ·
    refine ⟨915012877269212127488543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2440034339384565673302781 915012877269212127488543)
    ·
      refine ⟨1372519315903818191232815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 915012877269212127488543 1372519315903818191232815)
      ·
        refine ⟨2058778973855727286849223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1372519315903818191232815 2058778973855727286849223)
        ·
          refine ⟨3088168460783590930273835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058778973855727286849223 3088168460783590930273835)
          ·
            refine ⟨4632252691175386395410753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3088168460783590930273835 4632252691175386395410753)
            ·
              refine ⟨3474189518381539796558065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4632252691175386395410753 3474189518381539796558065)
              ·
                refine ⟨2605642138786154847418549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3474189518381539796558065 2605642138786154847418549)
                ·
                  refine ⟨244278950511202016945489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2605642138786154847418549 244278950511202016945489)
                  ·
                    rfl

theorem cell20_535198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_535198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535198 prefixEnd_535198 := by exact prefixLift 535198
  have htrace : WordTrace (prefixWord ++ tailWord_535198) baseStart_535198 baseEnd_535198 := by
    simpa [prefixWord, tailWord_535198, baseEnd_535198] using wordTrace_append hprefix tailTrace_535198
  have hstable : (prefixWord ++ tailWord_535198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535198).length < 2 ^ (prefixWord ++ tailWord_535198).sum := by decide
  have hdescent : baseEnd_535198 < baseStart_535198 := by decide
  rcases family_descends (prefixWord ++ tailWord_535198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535201 : List Nat := [1, 2, 3, 3, 3, 1, 2, 3, 2]
def baseStart_535201 : Nat := 118140960795 + 535201 * 2 ^ 59
def prefixEnd_535201 : Nat := 4983230072969 + 3 ^ 40 * 535201 * 2
def baseEnd_535201 : Nat := 244280319792947339845477

theorem tailTrace_535201 : CollatzResearch.WordTrace tailWord_535201 prefixEnd_535201 244280319792947339845477 := by
  unfold tailWord_535201
  simp only [CollatzResearch.WordTrace]
  refine ⟨19520384134065656898781457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13013589422710437932520971 19520384134065656898781457)
  ·
    refine ⟨14640288100549242674086093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19520384134065656898781457 14640288100549242674086093)
    ·
      refine ⟨5490108037705966002782285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14640288100549242674086093 5490108037705966002782285)
      ·
        refine ⟨2058790514139737251043357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5490108037705966002782285 2058790514139737251043357)
        ·
          refine ⟨772046442802401469141259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2058790514139737251043357 772046442802401469141259)
          ·
            refine ⟨1158069664203602203711889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772046442802401469141259 1158069664203602203711889)
            ·
              refine ⟨868552248152701652783917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1158069664203602203711889 868552248152701652783917)
              ·
                refine ⟨325707093057263119793969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 868552248152701652783917 325707093057263119793969)
                ·
                  refine ⟨244280319792947339845477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325707093057263119793969 244280319792947339845477)
                  ·
                    rfl

theorem cell20_535201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 2].length) (baseStart_535201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535201 prefixEnd_535201 := by exact prefixLift 535201
  have htrace : WordTrace (prefixWord ++ tailWord_535201) baseStart_535201 baseEnd_535201 := by
    simpa [prefixWord, tailWord_535201, baseEnd_535201] using wordTrace_append hprefix tailTrace_535201
  have hstable : (prefixWord ++ tailWord_535201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535201).length < 2 ^ (prefixWord ++ tailWord_535201).sum := by decide
  have hdescent : baseEnd_535201 < baseStart_535201 := by decide
  rcases family_descends (prefixWord ++ tailWord_535201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535219 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 5]
def baseStart_535219 : Nat := 118140960795 + 535219 * 2 ^ 59
def prefixEnd_535219 : Nat := 4983230072969 + 3 ^ 40 * 535219 * 2
def baseEnd_535219 : Nat := 244288535483419277245403

theorem tailTrace_535219 : CollatzResearch.WordTrace tailWord_535219 prefixEnd_535219 244288535483419277245403 := by
  unfold tailWord_535219
  simp only [CollatzResearch.WordTrace]
  refine ⟨19521040648000445972936711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13014027098666963981957807 19521040648000445972936711)
  ·
    refine ⟨29281560972000668959405067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19521040648000445972936711 29281560972000668959405067)
    ·
      refine ⟨43922341458001003439107601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29281560972000668959405067 43922341458001003439107601)
      ·
        refine ⟨32941756093500752579330701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43922341458001003439107601 32941756093500752579330701)
        ·
          refine ⟨12353158535062782217249013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32941756093500752579330701 12353158535062782217249013)
          ·
            refine ⟨1158108612662135832867095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12353158535062782217249013 1158108612662135832867095)
            ·
              refine ⟨1737162918993203749300643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158108612662135832867095 1737162918993203749300643)
              ·
                refine ⟨2605744378489805623950965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1737162918993203749300643 2605744378489805623950965)
                ·
                  refine ⟨244288535483419277245403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2605744378489805623950965 244288535483419277245403)
                  ·
                    rfl

theorem cell20_535219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 5].length) (baseStart_535219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535219 prefixEnd_535219 := by exact prefixLift 535219
  have htrace : WordTrace (prefixWord ++ tailWord_535219) baseStart_535219 baseEnd_535219 := by
    simpa [prefixWord, tailWord_535219, baseEnd_535219] using wordTrace_append hprefix tailTrace_535219
  have hstable : (prefixWord ++ tailWord_535219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535219).length < 2 ^ (prefixWord ++ tailWord_535219).sum := by decide
  have hdescent : baseEnd_535219 < baseStart_535219 := by decide
  rcases family_descends (prefixWord ++ tailWord_535219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535277 : List Nat := [1, 5, 1, 2, 1, 1, 5, 2, 2]
def baseStart_535277 : Nat := 118140960795 + 535277 * 2 ^ 59
def prefixEnd_535277 : Nat := 4983230072969 + 3 ^ 40 * 535277 * 2
def baseEnd_535277 : Nat := 244315008263828853311833

theorem tailTrace_535277 : CollatzResearch.WordTrace tailWord_535277 prefixEnd_535277 244315008263828853311833 := by
  unfold tailWord_535277
  simp only [CollatzResearch.WordTrace]
  refine ⟨19523156081790321878548085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13015437387860214585698723 19523156081790321878548085)
  ·
    refine ⟨1830295882667842676113883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19523156081790321878548085 1830295882667842676113883)
    ·
      refine ⟨2745443824001764014170825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1830295882667842676113883 2745443824001764014170825)
      ·
        refine ⟨2059082868001323010628119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2745443824001764014170825 2059082868001323010628119)
        ·
          refine ⟨3088624302001984515942179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2059082868001323010628119 3088624302001984515942179)
          ·
            refine ⟨4632936453002976773913269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3088624302001984515942179 4632936453002976773913269)
            ·
              refine ⟨434337792469029072554369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4632936453002976773913269 434337792469029072554369)
              ·
                refine ⟨325753344351771804415777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434337792469029072554369 325753344351771804415777)
                ·
                  refine ⟨244315008263828853311833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325753344351771804415777 244315008263828853311833)
                  ·
                    rfl

theorem cell20_535277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_535277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535277 prefixEnd_535277 := by exact prefixLift 535277
  have htrace : WordTrace (prefixWord ++ tailWord_535277) baseStart_535277 baseEnd_535277 := by
    simpa [prefixWord, tailWord_535277, baseEnd_535277] using wordTrace_append hprefix tailTrace_535277
  have hstable : (prefixWord ++ tailWord_535277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535277).length < 2 ^ (prefixWord ++ tailWord_535277).sum := by decide
  have hdescent : baseEnd_535277 < baseStart_535277 := by decide
  rcases family_descends (prefixWord ++ tailWord_535277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535326 : List Nat := [4, 3, 2, 11]
def baseStart_535326 : Nat := 118140960795 + 535326 * 2 ^ 59
def prefixEnd_535326 : Nat := 4983230072969 + 3 ^ 40 * 535326 * 2
def baseEnd_535326 : Nat := 1005503593411532759993

theorem tailTrace_535326 : CollatzResearch.WordTrace tailWord_535326 prefixEnd_535326 1005503593411532759993 := by
  unfold tailWord_535326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2440617907326600405885229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13016628839075202164721221 2440617907326600405885229)
  ·
    refine ⟨915231715247475152206961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2440617907326600405885229 915231715247475152206961)
    ·
      refine ⟨686423786435606364155221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 915231715247475152206961 686423786435606364155221)
      ·
        refine ⟨1005503593411532759993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 686423786435606364155221 1005503593411532759993)
        ·
          rfl

theorem cell20_535326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 11].length) (baseStart_535326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535326 prefixEnd_535326 := by exact prefixLift 535326
  have htrace : WordTrace (prefixWord ++ tailWord_535326) baseStart_535326 baseEnd_535326 := by
    simpa [prefixWord, tailWord_535326, baseEnd_535326] using wordTrace_append hprefix tailTrace_535326
  have hstable : (prefixWord ++ tailWord_535326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535326).length < 2 ^ (prefixWord ++ tailWord_535326).sum := by decide
  have hdescent : baseEnd_535326 < baseStart_535326 := by decide
  rcases family_descends (prefixWord ++ tailWord_535326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535332 : List Nat := [2, 3, 1, 3, 3, 2, 2, 2, 2]
def baseStart_535332 : Nat := 118140960795 + 535332 * 2 ^ 59
def prefixEnd_535332 : Nat := 4983230072969 + 3 ^ 40 * 535332 * 2
def baseEnd_535332 : Nat := 244340111762493106478275

theorem tailTrace_535332 : CollatzResearch.WordTrace tailWord_535332 prefixEnd_535332 244340111762493106478275 := by
  unfold tailWord_535332
  simp only [CollatzResearch.WordTrace]
  refine ⟨9762581048295533135900125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13016774731060710847866833 9762581048295533135900125)
  ·
    refine ⟨3660967893110824925962547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9762581048295533135900125 3660967893110824925962547)
    ·
      refine ⟨5491451839666237388943821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3660967893110824925962547 5491451839666237388943821)
      ·
        refine ⟨2059294439874839020853933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5491451839666237388943821 2059294439874839020853933)
        ·
          refine ⟨772235414953064632820225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2059294439874839020853933 772235414953064632820225)
          ·
            refine ⟨579176561214798474615169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 772235414953064632820225 579176561214798474615169)
            ·
              refine ⟨434382420911098855961377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579176561214798474615169 434382420911098855961377)
              ·
                refine ⟨325786815683324141971033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434382420911098855961377 325786815683324141971033)
                ·
                  refine ⟨244340111762493106478275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325786815683324141971033 244340111762493106478275)
                  ·
                    rfl

theorem cell20_535332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_535332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535332 prefixEnd_535332 := by exact prefixLift 535332
  have htrace : WordTrace (prefixWord ++ tailWord_535332) baseStart_535332 baseEnd_535332 := by
    simpa [prefixWord, tailWord_535332, baseEnd_535332] using wordTrace_append hprefix tailTrace_535332
  have hstable : (prefixWord ++ tailWord_535332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535332).length < 2 ^ (prefixWord ++ tailWord_535332).sum := by decide
  have hdescent : baseEnd_535332 < baseStart_535332 := by decide
  rcases family_descends (prefixWord ++ tailWord_535332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535336 : List Nat := [2, 1, 5, 1, 1, 1, 3, 4, 2]
def baseStart_535336 : Nat := 118140960795 + 535336 * 2 ^ 59
def prefixEnd_535336 : Nat := 4983230072969 + 3 ^ 40 * 535336 * 2
def baseEnd_535336 : Nat := 244341937471486870344925

theorem tailTrace_535336 : CollatzResearch.WordTrace tailWord_535336 prefixEnd_535336 244341937471486870344925 := by
  unfold tailWord_535336
  simp only [CollatzResearch.WordTrace]
  refine ⟨9762653994288287477472931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13016871992384383303297241 9762653994288287477472931)
  ·
    refine ⟨14643980991432431216209397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9762653994288287477472931 14643980991432431216209397)
    ·
      refine ⟨1372873217946790426519631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14643980991432431216209397 1372873217946790426519631)
      ·
        refine ⟨2059309826920185639779447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1372873217946790426519631 2059309826920185639779447)
        ·
          refine ⟨3088964740380278459669171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2059309826920185639779447 3088964740380278459669171)
          ·
            refine ⟨4633447110570417689503757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3088964740380278459669171 4633447110570417689503757)
            ·
              refine ⟨1737542666463906633563909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4633447110570417689503757 1737542666463906633563909)
              ·
                refine ⟨325789249961982493793233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1737542666463906633563909 325789249961982493793233)
                ·
                  refine ⟨244341937471486870344925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325789249961982493793233 244341937471486870344925)
                  ·
                    rfl

theorem cell20_535336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 2].length) (baseStart_535336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535336 prefixEnd_535336 := by exact prefixLift 535336
  have htrace : WordTrace (prefixWord ++ tailWord_535336) baseStart_535336 baseEnd_535336 := by
    simpa [prefixWord, tailWord_535336, baseEnd_535336] using wordTrace_append hprefix tailTrace_535336
  have hstable : (prefixWord ++ tailWord_535336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535336).length < 2 ^ (prefixWord ++ tailWord_535336).sum := by decide
  have hdescent : baseEnd_535336 < baseStart_535336 := by decide
  rcases family_descends (prefixWord ++ tailWord_535336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535340 : List Nat := [2, 2, 1, 1, 1, 4, 2, 3, 4]
def baseStart_535340 : Nat := 118140960795 + 535340 * 2 ^ 59
def prefixEnd_535340 : Nat := 4983230072969 + 3 ^ 40 * 535340 * 2
def baseEnd_535340 : Nat := 244343763180480634211575

theorem tailTrace_535340 : CollatzResearch.WordTrace tailWord_535340 prefixEnd_535340 244343763180480634211575 := by
  unfold tailWord_535340
  simp only [CollatzResearch.WordTrace]
  refine ⟨9762726940281041819045737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13016969253708055758727649 9762726940281041819045737)
  ·
    refine ⟨7322045205210781364284303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9762726940281041819045737 7322045205210781364284303)
    ·
      refine ⟨10983067807816172046426455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7322045205210781364284303 10983067807816172046426455)
      ·
        refine ⟨16474601711724258069639683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10983067807816172046426455 16474601711724258069639683)
        ·
          refine ⟨24711902567586387104459525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16474601711724258069639683 24711902567586387104459525)
          ·
            refine ⟨4633481731422447582086161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24711902567586387104459525 4633481731422447582086161)
            ·
              refine ⟨3475111298566835686564621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4633481731422447582086161 3475111298566835686564621)
              ·
                refine ⟨1303166736962563382461733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3475111298566835686564621 1303166736962563382461733)
                ·
                  refine ⟨244343763180480634211575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1303166736962563382461733 244343763180480634211575)
                  ·
                    rfl

theorem cell20_535340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_535340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535340 prefixEnd_535340 := by exact prefixLift 535340
  have htrace : WordTrace (prefixWord ++ tailWord_535340) baseStart_535340 baseEnd_535340 := by
    simpa [prefixWord, tailWord_535340, baseEnd_535340] using wordTrace_append hprefix tailTrace_535340
  have hstable : (prefixWord ++ tailWord_535340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535340).length < 2 ^ (prefixWord ++ tailWord_535340).sum := by decide
  have hdescent : baseEnd_535340 < baseStart_535340 := by decide
  rcases family_descends (prefixWord ++ tailWord_535340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535378 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_535378 : Nat := 118140960795 + 535378 * 2 ^ 59
def prefixEnd_535378 : Nat := 4983230072969 + 3 ^ 40 * 535378 * 2
def baseEnd_535378 : Nat := 244361107415921390944753

theorem tailTrace_535378 : CollatzResearch.WordTrace tailWord_535378 prefixEnd_535378 244361107415921390944753 := by
  unfold tailWord_535378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4881709963606104031993697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13017893236282944085316525 4881709963606104031993697)
  ·
    refine ⟨3661282472704578023995273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4881709963606104031993697 3661282472704578023995273)
    ·
      refine ⟨2745961854528433517996455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3661282472704578023995273 2745961854528433517996455)
      ·
        refine ⟨4118942781792650276994683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2745961854528433517996455 4118942781792650276994683)
        ·
          refine ⟨6178414172688975415492025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4118942781792650276994683 6178414172688975415492025)
          ·
            refine ⟨4633810629516731561619019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6178414172688975415492025 4633810629516731561619019)
            ·
              refine ⟨6950715944275097342428529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4633810629516731561619019 6950715944275097342428529)
              ·
                refine ⟨5213036958206323006821397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6950715944275097342428529 5213036958206323006821397)
                ·
                  refine ⟨244361107415921390944753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5213036958206323006821397 244361107415921390944753)
                  ·
                    rfl

theorem cell20_535378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_535378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535378 prefixEnd_535378 := by exact prefixLift 535378
  have htrace : WordTrace (prefixWord ++ tailWord_535378) baseStart_535378 baseEnd_535378 := by
    simpa [prefixWord, tailWord_535378, baseEnd_535378] using wordTrace_append hprefix tailTrace_535378
  have hstable : (prefixWord ++ tailWord_535378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535378).length < 2 ^ (prefixWord ++ tailWord_535378).sum := by decide
  have hdescent : baseEnd_535378 < baseStart_535378 := by decide
  rcases family_descends (prefixWord ++ tailWord_535378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535385 : List Nat := [1, 2, 1, 2, 2, 5, 7]
def baseStart_535385 : Nat := 118140960795 + 535385 * 2 ^ 59
def prefixEnd_535385 : Nat := 4983230072969 + 3 ^ 40 * 535385 * 2
def baseEnd_535385 : Nat := 27151589156295608634599

theorem tailTrace_535385 : CollatzResearch.WordTrace tailWord_535385 prefixEnd_535385 27151589156295608634599 := by
  unfold tailWord_535385
  simp only [CollatzResearch.WordTrace]
  refine ⟨19527095165399056323479609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13018063443599370882319739 19527095165399056323479609)
  ·
    refine ⟨14645321374049292242609707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19527095165399056323479609 14645321374049292242609707)
    ·
      refine ⟨21967982061073938363914561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14645321374049292242609707 21967982061073938363914561)
      ·
        refine ⟨16475986545805453772935921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21967982061073938363914561 16475986545805453772935921)
        ·
          refine ⟨12356989909354090329701941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16475986545805453772935921 12356989909354090329701941)
          ·
            refine ⟨1158467804001945968409557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12356989909354090329701941 1158467804001945968409557)
            ·
              refine ⟨27151589156295608634599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1158467804001945968409557 27151589156295608634599)
              ·
                rfl

theorem cell20_535385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 7].length) (baseStart_535385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535385 prefixEnd_535385 := by exact prefixLift 535385
  have htrace : WordTrace (prefixWord ++ tailWord_535385) baseStart_535385 baseEnd_535385 := by
    simpa [prefixWord, tailWord_535385, baseEnd_535385] using wordTrace_append hprefix tailTrace_535385
  have hstable : (prefixWord ++ tailWord_535385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535385).length < 2 ^ (prefixWord ++ tailWord_535385).sum := by decide
  have hdescent : baseEnd_535385 < baseStart_535385 := by decide
  rcases family_descends (prefixWord ++ tailWord_535385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535388 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 5]
def baseStart_535388 : Nat := 118140960795 + 535388 * 2 ^ 59
def prefixEnd_535388 : Nat := 4983230072969 + 3 ^ 40 * 535388 * 2
def baseEnd_535388 : Nat := 244365671688405800611379

theorem tailTrace_535388 : CollatzResearch.WordTrace tailWord_535388 prefixEnd_535388 244365671688405800611379 := by
  unfold tailWord_535388
  simp only [CollatzResearch.WordTrace]
  refine ⟨9763602292194093917919409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13018136389592125223892545 9763602292194093917919409)
  ·
    refine ⟨7322701719145570438439557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9763602292194093917919409 7322701719145570438439557)
    ·
      refine ⟨1373006572339794457207417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7322701719145570438439557 1373006572339794457207417)
      ·
        refine ⟨1029754929254845842905563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1373006572339794457207417 1029754929254845842905563)
        ·
          refine ⟨1544632393882268764358345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029754929254845842905563 1544632393882268764358345)
          ·
            refine ⟨1158474295411701573268759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1544632393882268764358345 1158474295411701573268759)
            ·
              refine ⟨1737711443117552359903139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158474295411701573268759 1737711443117552359903139)
              ·
                refine ⟨2606567164676328539854709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1737711443117552359903139 2606567164676328539854709)
                ·
                  refine ⟨244365671688405800611379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2606567164676328539854709 244365671688405800611379)
                  ·
                    rfl

theorem cell20_535388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_535388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535388 prefixEnd_535388 := by exact prefixLift 535388
  have htrace : WordTrace (prefixWord ++ tailWord_535388) baseStart_535388 baseEnd_535388 := by
    simpa [prefixWord, tailWord_535388, baseEnd_535388] using wordTrace_append hprefix tailTrace_535388
  have hstable : (prefixWord ++ tailWord_535388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535388).length < 2 ^ (prefixWord ++ tailWord_535388).sum := by decide
  have hdescent : baseEnd_535388 < baseStart_535388 := by decide
  rcases family_descends (prefixWord ++ tailWord_535388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535395 : List Nat := [1, 1, 1, 5, 3, 2, 2, 1, 4]
def baseStart_535395 : Nat := 118140960795 + 535395 * 2 ^ 59
def prefixEnd_535395 : Nat := 4983230072969 + 3 ^ 40 * 535395 * 2
def baseEnd_535395 : Nat := 244368866679144887378017

theorem tailTrace_535395 : CollatzResearch.WordTrace tailWord_535395 prefixEnd_535395 244368866679144887378017 := by
  unfold tailWord_535395
  simp only [CollatzResearch.WordTrace]
  refine ⟨19527459895362828031343639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13018306596908552020895759 19527459895362828031343639)
  ·
    refine ⟨29291189843044242047015459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19527459895362828031343639 29291189843044242047015459)
    ·
      refine ⟨43936784764566363070523189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29291189843044242047015459 43936784764566363070523189)
      ·
        refine ⟨4119073571678096537861549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43936784764566363070523189 4119073571678096537861549)
        ·
          refine ⟨1544652589379286201698081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4119073571678096537861549 1544652589379286201698081)
          ·
            refine ⟨1158489442034464651273561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1544652589379286201698081 1158489442034464651273561)
            ·
              refine ⟨868867081525848488455171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1158489442034464651273561 868867081525848488455171)
              ·
                refine ⟨1303300622288772732682757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868867081525848488455171 1303300622288772732682757)
                ·
                  refine ⟨244368866679144887378017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1303300622288772732682757 244368866679144887378017)
                  ·
                    rfl

theorem cell20_535395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 4].length) (baseStart_535395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535395 prefixEnd_535395 := by exact prefixLift 535395
  have htrace : WordTrace (prefixWord ++ tailWord_535395) baseStart_535395 baseEnd_535395 := by
    simpa [prefixWord, tailWord_535395, baseEnd_535395] using wordTrace_append hprefix tailTrace_535395
  have hstable : (prefixWord ++ tailWord_535395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535395).length < 2 ^ (prefixWord ++ tailWord_535395).sum := by decide
  have hdescent : baseEnd_535395 < baseStart_535395 := by decide
  rcases family_descends (prefixWord ++ tailWord_535395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535446 : List Nat := [5, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_535446 : Nat := 118140960795 + 535446 * 2 ^ 59
def prefixEnd_535446 : Nat := 4983230072969 + 3 ^ 40 * 535446 * 2
def baseEnd_535446 : Nat := 244392144468815376677809

theorem tailTrace_535446 : CollatzResearch.WordTrace tailWord_535446 prefixEnd_535446 244392144468815376677809 := by
  unfold tailWord_535446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1220582501136128983840637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13019546678785375827633461 1220582501136128983840637)
  ·
    refine ⟨457718437926048368940239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1220582501136128983840637 457718437926048368940239)
    ·
      refine ⟨686577656889072553410359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457718437926048368940239 686577656889072553410359)
      ·
        refine ⟨1029866485333608830115539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686577656889072553410359 1029866485333608830115539)
        ·
          refine ⟨1544799728000413245173309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029866485333608830115539 1544799728000413245173309)
          ·
            refine ⟨579299898000154966939991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1544799728000413245173309 579299898000154966939991)
            ·
              refine ⟨868949847000232450409987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579299898000154966939991 868949847000232450409987)
              ·
                refine ⟨1303424770500348675614981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868949847000232450409987 1303424770500348675614981)
                ·
                  refine ⟨244392144468815376677809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1303424770500348675614981 244392144468815376677809)
                  ·
                    rfl

theorem cell20_535446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_535446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535446 prefixEnd_535446 := by exact prefixLift 535446
  have htrace : WordTrace (prefixWord ++ tailWord_535446) baseStart_535446 baseEnd_535446 := by
    simpa [prefixWord, tailWord_535446, baseEnd_535446] using wordTrace_append hprefix tailTrace_535446
  have hstable : (prefixWord ++ tailWord_535446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535446).length < 2 ^ (prefixWord ++ tailWord_535446).sum := by decide
  have hdescent : baseEnd_535446 < baseStart_535446 := by decide
  rcases family_descends (prefixWord ++ tailWord_535446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535447 : List Nat := [1, 1, 3, 3, 1, 2, 2, 4, 3]
def baseStart_535447 : Nat := 118140960795 + 535447 * 2 ^ 59
def prefixEnd_535447 : Nat := 4983230072969 + 3 ^ 40 * 535447 * 2
def baseEnd_535447 : Nat := 244392600896063817644471

theorem tailTrace_535447 : CollatzResearch.WordTrace tailWord_535447 prefixEnd_535447 244392600896063817644471 := by
  unfold tailWord_535447
  simp only [CollatzResearch.WordTrace]
  refine ⟨19529356491174440912236595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13019570994116293941491063 19529356491174440912236595)
  ·
    refine ⟨29294034736761661368354893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19529356491174440912236595 29294034736761661368354893)
    ·
      refine ⟨10985263026285623013133085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29294034736761661368354893 10985263026285623013133085)
      ·
        refine ⟨4119473634857108629924907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10985263026285623013133085 4119473634857108629924907)
        ·
          refine ⟨6179210452285662944887361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4119473634857108629924907 6179210452285662944887361)
          ·
            refine ⟨4634407839214247208665521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6179210452285662944887361 4634407839214247208665521)
            ·
              refine ⟨3475805879410685406499141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4634407839214247208665521 3475805879410685406499141)
              ·
                refine ⟨651713602389503513718589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3475805879410685406499141 651713602389503513718589)
                ·
                  refine ⟨244392600896063817644471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651713602389503513718589 244392600896063817644471)
                  ·
                    rfl

theorem cell20_535447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 3].length) (baseStart_535447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535447 prefixEnd_535447 := by exact prefixLift 535447
  have htrace : WordTrace (prefixWord ++ tailWord_535447) baseStart_535447 baseEnd_535447 := by
    simpa [prefixWord, tailWord_535447, baseEnd_535447] using wordTrace_append hprefix tailTrace_535447
  have hstable : (prefixWord ++ tailWord_535447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535447).length < 2 ^ (prefixWord ++ tailWord_535447).sum := by decide
  have hdescent : baseEnd_535447 < baseStart_535447 := by decide
  rcases family_descends (prefixWord ++ tailWord_535447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535450 : List Nat := [3, 1, 1, 4, 3, 2, 1, 1, 4]
def baseStart_535450 : Nat := 118140960795 + 535450 * 2 ^ 59
def prefixEnd_535450 : Nat := 4983230072969 + 3 ^ 40 * 535450 * 2
def baseEnd_535450 : Nat := 244393970177809140544459

theorem tailTrace_535450 : CollatzResearch.WordTrace tailWord_535450 prefixEnd_535450 244393970177809140544459 := by
  unfold tailWord_535450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4882366477540893106148951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13019643940109048283063869 4882366477540893106148951)
  ·
    refine ⟨7323549716311339659223427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4882366477540893106148951 7323549716311339659223427)
    ·
      refine ⟨10985324574467009488835141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7323549716311339659223427 10985324574467009488835141)
      ·
        refine ⟨2059748357712564279156589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10985324574467009488835141 2059748357712564279156589)
        ·
          refine ⟨772405634142211604683721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2059748357712564279156589 772405634142211604683721)
          ·
            refine ⟨579304225606658703512791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 772405634142211604683721 579304225606658703512791)
            ·
              refine ⟨868956338409988055269187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579304225606658703512791 868956338409988055269187)
              ·
                refine ⟨1303434507614982082903781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868956338409988055269187 1303434507614982082903781)
                ·
                  refine ⟨244393970177809140544459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1303434507614982082903781 244393970177809140544459)
                  ·
                    rfl

theorem cell20_535450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_535450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535450 prefixEnd_535450 := by exact prefixLift 535450
  have htrace : WordTrace (prefixWord ++ tailWord_535450) baseStart_535450 baseEnd_535450 := by
    simpa [prefixWord, tailWord_535450, baseEnd_535450] using wordTrace_append hprefix tailTrace_535450
  have hstable : (prefixWord ++ tailWord_535450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535450).length < 2 ^ (prefixWord ++ tailWord_535450).sum := by decide
  have hdescent : baseEnd_535450 < baseStart_535450 := by decide
  rcases family_descends (prefixWord ++ tailWord_535450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535494 : List Nat := [6, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_535494 : Nat := 118140960795 + 535494 * 2 ^ 59
def prefixEnd_535494 : Nat := 4983230072969 + 3 ^ 40 * 535494 * 2
def baseEnd_535494 : Nat := 244414052976740543077613

theorem tailTrace_535494 : CollatzResearch.WordTrace tailWord_535494 prefixEnd_535494 244414052976740543077613 := by
  unfold tailWord_535494
  simp only [CollatzResearch.WordTrace]
  refine ⟨610345960062630248099923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13020713814669445292798357 610345960062630248099923)
  ·
    refine ⟨915518940093945372149885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 610345960062630248099923 915518940093945372149885)
    ·
      refine ⟨343319602535229514556207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 915518940093945372149885 343319602535229514556207)
      ·
        refine ⟨514979403802844271834311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343319602535229514556207 514979403802844271834311)
        ·
          refine ⟨772469105704266407751467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514979403802844271834311 772469105704266407751467)
          ·
            refine ⟨1158703658556399611627201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772469105704266407751467 1158703658556399611627201)
            ·
              refine ⟨869027743917299708720401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1158703658556399611627201 869027743917299708720401)
              ·
                refine ⟨651770807937974781540301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869027743917299708720401 651770807937974781540301)
                ·
                  refine ⟨244414052976740543077613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651770807937974781540301 244414052976740543077613)
                  ·
                    rfl

theorem cell20_535494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_535494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535494 prefixEnd_535494 := by exact prefixLift 535494
  have htrace : WordTrace (prefixWord ++ tailWord_535494) baseStart_535494 baseEnd_535494 := by
    simpa [prefixWord, tailWord_535494, baseEnd_535494] using wordTrace_append hprefix tailTrace_535494
  have hstable : (prefixWord ++ tailWord_535494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535494).length < 2 ^ (prefixWord ++ tailWord_535494).sum := by decide
  have hdescent : baseEnd_535494 < baseStart_535494 := by decide
  rcases family_descends (prefixWord ++ tailWord_535494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535501 : List Nat := [1, 6, 3, 1, 1, 1, 1, 4, 2]
def baseStart_535501 : Nat := 118140960795 + 535501 * 2 ^ 59
def prefixEnd_535501 : Nat := 4983230072969 + 3 ^ 40 * 535501 * 2
def baseEnd_535501 : Nat := 244417247967479629844251

theorem tailTrace_535501 : CollatzResearch.WordTrace tailWord_535501 prefixEnd_535501 244417247967479629844251 := by
  unfold tailWord_535501
  simp only [CollatzResearch.WordTrace]
  refine ⟨19531326032978808134702357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13020884021985872089801571 19531326032978808134702357)
  ·
    refine ⟨915530907795881631314173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19531326032978808134702357 915530907795881631314173)
    ·
      refine ⟨343324090423455611742815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 915530907795881631314173 343324090423455611742815)
      ·
        refine ⟨514986135635183417614223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343324090423455611742815 514986135635183417614223)
        ·
          refine ⟨772479203452775126421335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514986135635183417614223 772479203452775126421335)
          ·
            refine ⟨1158718805179162689632003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772479203452775126421335 1158718805179162689632003)
            ·
              refine ⟨1738078207768744034448005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158718805179162689632003 1738078207768744034448005)
              ·
                refine ⟨325889663956639506459001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1738078207768744034448005 325889663956639506459001)
                ·
                  refine ⟨244417247967479629844251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325889663956639506459001 244417247967479629844251)
                  ·
                    rfl

theorem cell20_535501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_535501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535501 prefixEnd_535501 := by exact prefixLift 535501
  have htrace : WordTrace (prefixWord ++ tailWord_535501) baseStart_535501 baseEnd_535501 := by
    simpa [prefixWord, tailWord_535501, baseEnd_535501] using wordTrace_append hprefix tailTrace_535501
  have hstable : (prefixWord ++ tailWord_535501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535501).length < 2 ^ (prefixWord ++ tailWord_535501).sum := by decide
  have hdescent : baseEnd_535501 < baseStart_535501 := by decide
  rcases family_descends (prefixWord ++ tailWord_535501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535502 : List Nat := [4, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_535502 : Nat := 118140960795 + 535502 * 2 ^ 59
def prefixEnd_535502 : Nat := 4983230072969 + 3 ^ 40 * 535502 * 2
def baseEnd_535502 : Nat := 244417704394728070810913

theorem tailTrace_535502 : CollatzResearch.WordTrace tailWord_535502 prefixEnd_535502 244417704394728070810913 := by
  unfold tailWord_535502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2441420313246898163186095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13020908337316790203659173 2441420313246898163186095)
  ·
    refine ⟨3662130469870347244779143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2441420313246898163186095 3662130469870347244779143)
    ·
      refine ⟨5493195704805520867168715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3662130469870347244779143 5493195704805520867168715)
      ·
        refine ⟨8239793557208281300753073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5493195704805520867168715 8239793557208281300753073)
        ·
          refine ⟨6179845167906210975564805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8239793557208281300753073 6179845167906210975564805)
          ·
            refine ⟨1158720968982414557918401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6179845167906210975564805 1158720968982414557918401)
            ·
              refine ⟨869040726736810918438801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1158720968982414557918401 869040726736810918438801)
              ·
                refine ⟨651780545052608188829101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869040726736810918438801 651780545052608188829101)
                ·
                  refine ⟨244417704394728070810913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651780545052608188829101 244417704394728070810913)
                  ·
                    rfl

theorem cell20_535502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_535502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535502 prefixEnd_535502 := by exact prefixLift 535502
  have htrace : WordTrace (prefixWord ++ tailWord_535502) baseStart_535502 baseEnd_535502 := by
    simpa [prefixWord, tailWord_535502, baseEnd_535502] using wordTrace_append hprefix tailTrace_535502
  have hstable : (prefixWord ++ tailWord_535502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535502).length < 2 ^ (prefixWord ++ tailWord_535502).sum := by decide
  have hdescent : baseEnd_535502 < baseStart_535502 := by decide
  rcases family_descends (prefixWord ++ tailWord_535502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535523 : List Nat := [1, 1, 1, 6, 1, 1, 1, 5, 3]
def baseStart_535523 : Nat := 118140960795 + 535523 * 2 ^ 59
def prefixEnd_535523 : Nat := 4983230072969 + 3 ^ 40 * 535523 * 2
def baseEnd_535523 : Nat := 244427289366945331110827

theorem tailTrace_535523 : CollatzResearch.WordTrace tailWord_535523 prefixEnd_535523 244427289366945331110827 := by
  unfold tailWord_535523
  simp only [CollatzResearch.WordTrace]
  refine ⟨19532128438899105892003223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13021418959266070594668815 19532128438899105892003223)
  ·
    refine ⟨29298192658348658838004835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19532128438899105892003223 29298192658348658838004835)
    ·
      refine ⟨43947288987522988257007253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29298192658348658838004835 43947288987522988257007253)
      ·
        refine ⟨2060029171290140074547215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43947288987522988257007253 2060029171290140074547215)
        ·
          refine ⟨3090043756935210111820823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2060029171290140074547215 3090043756935210111820823)
          ·
            refine ⟨4635065635402815167731235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3090043756935210111820823 4635065635402815167731235)
            ·
              refine ⟨6952598453104222751596853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4635065635402815167731235 6952598453104222751596853)
              ·
                refine ⟨651806104978520882962205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6952598453104222751596853 651806104978520882962205)
                ·
                  refine ⟨244427289366945331110827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651806104978520882962205 244427289366945331110827)
                  ·
                    rfl

theorem cell20_535523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 3].length) (baseStart_535523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535523 prefixEnd_535523 := by exact prefixLift 535523
  have htrace : WordTrace (prefixWord ++ tailWord_535523) baseStart_535523 baseEnd_535523 := by
    simpa [prefixWord, tailWord_535523, baseEnd_535523] using wordTrace_append hprefix tailTrace_535523
  have hstable : (prefixWord ++ tailWord_535523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535523).length < 2 ^ (prefixWord ++ tailWord_535523).sum := by decide
  have hdescent : baseEnd_535523 < baseStart_535523 := by decide
  rcases family_descends (prefixWord ++ tailWord_535523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535530 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_535530 : Nat := 118140960795 + 535530 * 2 ^ 59
def prefixEnd_535530 : Nat := 4983230072969 + 3 ^ 40 * 535530 * 2
def baseEnd_535530 : Nat := 244430484357684417877465

theorem tailTrace_535530 : CollatzResearch.WordTrace tailWord_535530 prefixEnd_535530 244430484357684417877465 := by
  unfold tailWord_535530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4883095937468436521877011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13021589166582497391672029 4883095937468436521877011)
  ·
    refine ⟨7324643906202654782815517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4883095937468436521877011 7324643906202654782815517)
    ·
      refine ⟨2746741464825995543555819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7324643906202654782815517 2746741464825995543555819)
      ·
        refine ⟨4120112197238993315333729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2746741464825995543555819 4120112197238993315333729)
        ·
          refine ⟨3090084147929244986500297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4120112197238993315333729 3090084147929244986500297)
          ·
            refine ⟨2317563110946933739875223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3090084147929244986500297 2317563110946933739875223)
            ·
              refine ⟨3476344666420400609812835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2317563110946933739875223 3476344666420400609812835)
              ·
                refine ⟨5214516999630600914719253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3476344666420400609812835 5214516999630600914719253)
                ·
                  refine ⟨244430484357684417877465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5214516999630600914719253 244430484357684417877465)
                  ·
                    rfl

theorem cell20_535530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_535530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535530 prefixEnd_535530 := by exact prefixLift 535530
  have htrace : WordTrace (prefixWord ++ tailWord_535530) baseStart_535530 baseEnd_535530 := by
    simpa [prefixWord, tailWord_535530, baseEnd_535530] using wordTrace_append hprefix tailTrace_535530
  have hstable : (prefixWord ++ tailWord_535530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535530).length < 2 ^ (prefixWord ++ tailWord_535530).sum := by decide
  have hdescent : baseEnd_535530 < baseStart_535530 := by decide
  rcases family_descends (prefixWord ++ tailWord_535530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535544 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 5]
def baseStart_535544 : Nat := 118140960795 + 535544 * 2 ^ 59
def prefixEnd_535544 : Nat := 4983230072969 + 3 ^ 40 * 535544 * 2
def baseEnd_535544 : Nat := 244436874339162591410741

theorem tailTrace_535544 : CollatzResearch.WordTrace tailWord_535544 prefixEnd_535544 244436874339162591410741 := by
  unfold tailWord_535544
  simp only [CollatzResearch.WordTrace]
  refine ⟨9766447185911513239258843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13021929581215350985678457 9766447185911513239258843)
  ·
    refine ⟨14649670778867269858888265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9766447185911513239258843 14649670778867269858888265)
    ·
      refine ⟨10987253084150452394166199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14649670778867269858888265 10987253084150452394166199)
      ·
        refine ⟨16480879626225678591249299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10987253084150452394166199 16480879626225678591249299)
        ·
          refine ⟨24721319439338517886873949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16480879626225678591249299 24721319439338517886873949)
          ·
            refine ⟨9270494789751944207577731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24721319439338517886873949 9270494789751944207577731)
            ·
              refine ⟨13905742184627916311366597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9270494789751944207577731 13905742184627916311366597)
              ·
                refine ⟨2607326659617734308381237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13905742184627916311366597 2607326659617734308381237)
                ·
                  refine ⟨244436874339162591410741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2607326659617734308381237 244436874339162591410741)
                  ·
                    rfl

theorem cell20_535544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_535544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535544 prefixEnd_535544 := by exact prefixLift 535544
  have htrace : WordTrace (prefixWord ++ tailWord_535544) baseStart_535544 baseEnd_535544 := by
    simpa [prefixWord, tailWord_535544, baseEnd_535544] using wordTrace_append hprefix tailTrace_535544
  have hstable : (prefixWord ++ tailWord_535544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535544).length < 2 ^ (prefixWord ++ tailWord_535544).sum := by decide
  have hdescent : baseEnd_535544 < baseStart_535544 := by decide
  rcases family_descends (prefixWord ++ tailWord_535544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535578 : List Nat := [3, 1, 1, 3, 1, 2, 5, 1, 3]
def baseStart_535578 : Nat := 118140960795 + 535578 * 2 ^ 59
def prefixEnd_535578 : Nat := 4983230072969 + 3 ^ 40 * 535578 * 2
def baseEnd_535578 : Nat := 244452392865609584277269

theorem tailTrace_535578 : CollatzResearch.WordTrace tailWord_535578 prefixEnd_535578 244452392865609584277269 := by
  unfold tailWord_535578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4883533613424962571313847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13022756302466566856836925 4883533613424962571313847)
  ·
    refine ⟨7325300420137443856970771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4883533613424962571313847 7325300420137443856970771)
    ·
      refine ⟨10987950630206165785456157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7325300420137443856970771 10987950630206165785456157)
      ·
        refine ⟨4120481486327312169546059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10987950630206165785456157 4120481486327312169546059)
        ·
          refine ⟨6180722229490968254319089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4120481486327312169546059 6180722229490968254319089)
          ·
            refine ⟨4635541672118226190739317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6180722229490968254319089 4635541672118226190739317)
            ·
              refine ⟨434582031761083705381811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4635541672118226190739317 434582031761083705381811)
              ·
                refine ⟨651873047641625558072717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434582031761083705381811 651873047641625558072717)
                ·
                  refine ⟨244452392865609584277269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651873047641625558072717 244452392865609584277269)
                  ·
                    rfl

theorem cell20_535578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_535578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535578 prefixEnd_535578 := by exact prefixLift 535578
  have htrace : WordTrace (prefixWord ++ tailWord_535578) baseStart_535578 baseEnd_535578 := by
    simpa [prefixWord, tailWord_535578, baseEnd_535578] using wordTrace_append hprefix tailTrace_535578
  have hstable : (prefixWord ++ tailWord_535578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535578).length < 2 ^ (prefixWord ++ tailWord_535578).sum := by decide
  have hdescent : baseEnd_535578 < baseStart_535578 := by decide
  rcases family_descends (prefixWord ++ tailWord_535578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535613 : List Nat := [1, 4, 1, 3, 1, 2, 8]
def baseStart_535613 : Nat := 118140960795 + 535613 * 2 ^ 59
def prefixEnd_535613 : Nat := 4983230072969 + 3 ^ 40 * 535613 * 2
def baseEnd_535613 : Nat := 27163151979922779790051

theorem tailTrace_535613 : CollatzResearch.WordTrace tailWord_535613 prefixEnd_535613 27163151979922779790051 := by
  unfold tailWord_535613
  simp only [CollatzResearch.WordTrace]
  refine ⟨19535411008573051262779493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13023607339048700841852995 19535411008573051262779493)
  ·
    refine ⟨3662889564107447111771155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19535411008573051262779493 3662889564107447111771155)
    ·
      refine ⟨5494334346161170667656733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3662889564107447111771155 5494334346161170667656733)
      ·
        refine ⟨2060375379810439000371275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5494334346161170667656733 2060375379810439000371275)
        ·
          refine ⟨3090563069715658500556913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2060375379810439000371275 3090563069715658500556913)
          ·
            refine ⟨2317922302286743875417685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3090563069715658500556913 2317922302286743875417685)
            ·
              refine ⟨27163151979922779790051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2317922302286743875417685 27163151979922779790051)
              ·
                rfl

theorem cell20_535613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 8].length) (baseStart_535613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535613 prefixEnd_535613 := by exact prefixLift 535613
  have htrace : WordTrace (prefixWord ++ tailWord_535613) baseStart_535613 baseEnd_535613 := by
    simpa [prefixWord, tailWord_535613, baseEnd_535613] using wordTrace_append hprefix tailTrace_535613
  have hstable : (prefixWord ++ tailWord_535613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535613).length < 2 ^ (prefixWord ++ tailWord_535613).sum := by decide
  have hdescent : baseEnd_535613 < baseStart_535613 := by decide
  rcases family_descends (prefixWord ++ tailWord_535613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535623 : List Nat := [1, 1, 4, 1, 3, 4, 1, 1, 4]
def baseStart_535623 : Nat := 118140960795 + 535623 * 2 ^ 59
def prefixEnd_535623 : Nat := 4983230072969 + 3 ^ 40 * 535623 * 2
def baseEnd_535623 : Nat := 244472932091789427777085

theorem tailTrace_535623 : CollatzResearch.WordTrace tailWord_535623 prefixEnd_535623 244472932091789427777085 := by
  unfold tailWord_535623
  simp only [CollatzResearch.WordTrace]
  refine ⟨19535775738536822970643523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13023850492357881980429015 19535775738536822970643523)
  ·
    refine ⟨29303663607805234455965285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19535775738536822970643523 29303663607805234455965285)
    ·
      refine ⟨5494436926463481460493491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29303663607805234455965285 5494436926463481460493491)
      ·
        refine ⟨8241655389695222190740237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5494436926463481460493491 8241655389695222190740237)
        ·
          refine ⟨3090620771135708321527589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8241655389695222190740237 3090620771135708321527589)
          ·
            refine ⟨579491394587945310286423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3090620771135708321527589 579491394587945310286423)
            ·
              refine ⟨869237091881917965429635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579491394587945310286423 869237091881917965429635)
              ·
                refine ⟨1303855637822876948144453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869237091881917965429635 1303855637822876948144453)
                ·
                  refine ⟨244472932091789427777085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1303855637822876948144453 244472932091789427777085)
                  ·
                    rfl

theorem cell20_535623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 4].length) (baseStart_535623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535623 prefixEnd_535623 := by exact prefixLift 535623
  have htrace : WordTrace (prefixWord ++ tailWord_535623) baseStart_535623 baseEnd_535623 := by
    simpa [prefixWord, tailWord_535623, baseEnd_535623] using wordTrace_append hprefix tailTrace_535623
  have hstable : (prefixWord ++ tailWord_535623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535623).length < 2 ^ (prefixWord ++ tailWord_535623).sum := by decide
  have hdescent : baseEnd_535623 < baseStart_535623 := by decide
  rcases family_descends (prefixWord ++ tailWord_535623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535637 : List Nat := [1, 3, 2, 2, 1, 2, 3, 3, 3]
def baseStart_535637 : Nat := 118140960795 + 535637 * 2 ^ 59
def prefixEnd_535637 : Nat := 4983230072969 + 3 ^ 40 * 535637 * 2
def baseEnd_535637 : Nat := 244479322073267601310361

theorem tailTrace_535637 : CollatzResearch.WordTrace tailWord_535637 prefixEnd_535637 244479322073267601310361 := by
  unfold tailWord_535637
  simp only [CollatzResearch.WordTrace]
  refine ⟨19536286360486103361653165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13024190906990735574435443 19536286360486103361653165)
  ·
    refine ⟨7326107385182288760619937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19536286360486103361653165 7326107385182288760619937)
    ·
      refine ⟨5494580538886716570464953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7326107385182288760619937 5494580538886716570464953)
      ·
        refine ⟨4120935404165037427848715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5494580538886716570464953 4120935404165037427848715)
        ·
          refine ⟨6181403106247556141773073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4120935404165037427848715 6181403106247556141773073)
          ·
            refine ⟨4636052329685667106329805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6181403106247556141773073 4636052329685667106329805)
            ·
              refine ⟨1738519623632125164873677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4636052329685667106329805 1738519623632125164873677)
              ·
                refine ⟨651944858862046936827629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1738519623632125164873677 651944858862046936827629)
                ·
                  refine ⟨244479322073267601310361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651944858862046936827629 244479322073267601310361)
                  ·
                    rfl

theorem cell20_535637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_535637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535637 prefixEnd_535637 := by exact prefixLift 535637
  have htrace : WordTrace (prefixWord ++ tailWord_535637) baseStart_535637 baseEnd_535637 := by
    simpa [prefixWord, tailWord_535637, baseEnd_535637] using wordTrace_append hprefix tailTrace_535637
  have hstable : (prefixWord ++ tailWord_535637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535637).length < 2 ^ (prefixWord ++ tailWord_535637).sum := by decide
  have hdescent : baseEnd_535637 < baseStart_535637 := by decide
  rcases family_descends (prefixWord ++ tailWord_535637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535644 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 6]
def baseStart_535644 : Nat := 118140960795 + 535644 * 2 ^ 59
def prefixEnd_535644 : Nat := 4983230072969 + 3 ^ 40 * 535644 * 2
def baseEnd_535644 : Nat := 244482517064006688076999

theorem tailTrace_535644 : CollatzResearch.WordTrace tailWord_535644 prefixEnd_535644 244482517064006688076999 := by
  unfold tailWord_535644
  simp only [CollatzResearch.WordTrace]
  refine ⟨9768270835730371778578993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13024361114307162371438657 9768270835730371778578993)
  ·
    refine ⟨7326203126797778833934245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9768270835730371778578993 7326203126797778833934245)
    ·
      refine ⟨1373663086274583531362671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7326203126797778833934245 1373663086274583531362671)
      ·
        refine ⟨2060494629411875297044007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1373663086274583531362671 2060494629411875297044007)
        ·
          refine ⟨3090741944117812945566011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2060494629411875297044007 3090741944117812945566011)
          ·
            refine ⟨4636112916176719418349017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3090741944117812945566011 4636112916176719418349017)
            ·
              refine ⟨3477084687132539563761763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4636112916176719418349017 3477084687132539563761763)
              ·
                refine ⟨5215627030698809345642645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477084687132539563761763 5215627030698809345642645)
                ·
                  refine ⟨244482517064006688076999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5215627030698809345642645 244482517064006688076999)
                  ·
                    rfl

theorem cell20_535644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_535644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535644 prefixEnd_535644 := by exact prefixLift 535644
  have htrace : WordTrace (prefixWord ++ tailWord_535644) baseStart_535644 baseEnd_535644 := by
    simpa [prefixWord, tailWord_535644, baseEnd_535644] using wordTrace_append hprefix tailTrace_535644
  have hstable : (prefixWord ++ tailWord_535644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535644).length < 2 ^ (prefixWord ++ tailWord_535644).sum := by decide
  have hdescent : baseEnd_535644 < baseStart_535644 := by decide
  rcases family_descends (prefixWord ++ tailWord_535644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535665 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 8]
def baseStart_535665 : Nat := 118140960795 + 535665 * 2 ^ 59
def prefixEnd_535665 : Nat := 4983230072969 + 3 ^ 40 * 535665 * 2
def baseEnd_535665 : Nat := 244492102036223948376913

theorem tailTrace_535665 : CollatzResearch.WordTrace tailWord_535665 prefixEnd_535665 244492102036223948376913 := by
  unfold tailWord_535665
  simp only [CollatzResearch.WordTrace]
  refine ⟨19537307604384664143672449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13024871736256442762448299 19537307604384664143672449)
  ·
    refine ⟨14652980703288498107754337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19537307604384664143672449 14652980703288498107754337)
    ·
      refine ⟨10989735527466373580815753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14652980703288498107754337 10989735527466373580815753)
      ·
        refine ⟨8242301645599780185611815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10989735527466373580815753 8242301645599780185611815)
        ·
          refine ⟨12363452468399670278417723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8242301645599780185611815 12363452468399670278417723)
          ·
            refine ⟨18545178702599505417626585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12363452468399670278417723 18545178702599505417626585)
            ·
              refine ⟨13908884026949629063219939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18545178702599505417626585 13908884026949629063219939)
              ·
                refine ⟨20863326040424443594829909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13908884026949629063219939 20863326040424443594829909)
                ·
                  refine ⟨244492102036223948376913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20863326040424443594829909 244492102036223948376913)
                  ·
                    rfl

theorem cell20_535665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_535665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535665 prefixEnd_535665 := by exact prefixLift 535665
  have htrace : WordTrace (prefixWord ++ tailWord_535665) baseStart_535665 baseEnd_535665 := by
    simpa [prefixWord, tailWord_535665, baseEnd_535665] using wordTrace_append hprefix tailTrace_535665
  have hstable : (prefixWord ++ tailWord_535665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535665).length < 2 ^ (prefixWord ++ tailWord_535665).sum := by decide
  have hdescent : baseEnd_535665 < baseStart_535665 := by decide
  rcases family_descends (prefixWord ++ tailWord_535665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535685 : List Nat := [1, 3, 1, 1, 7, 1, 1, 5]
def baseStart_535685 : Nat := 118140960795 + 535685 * 2 ^ 59
def prefixEnd_535685 : Nat := 4983230072969 + 3 ^ 40 * 535685 * 2
def baseEnd_535685 : Nat := 81500410193730922570055

theorem tailTrace_535685 : CollatzResearch.WordTrace tailWord_535685 prefixEnd_535685 81500410193730922570055 := by
  unfold tailWord_535685
  simp only [CollatzResearch.WordTrace]
  refine ⟨19538037064312207559400509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13025358042874805039600339 19538037064312207559400509)
  ·
    refine ⟨7326763899117077834775191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19538037064312207559400509 7326763899117077834775191)
    ·
      refine ⟨10990145848675616752162787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7326763899117077834775191 10990145848675616752162787)
      ·
        refine ⟨16485218773013425128244181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10990145848675616752162787 16485218773013425128244181)
        ·
          refine ⟨386372314992502151443223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 16485218773013425128244181 386372314992502151443223)
          ·
            refine ⟨579558472488753227164835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386372314992502151443223 579558472488753227164835)
            ·
              refine ⟨869337708733129840747253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579558472488753227164835 869337708733129840747253)
              ·
                refine ⟨81500410193730922570055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 869337708733129840747253 81500410193730922570055)
                ·
                  rfl

theorem cell20_535685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 5].length) (baseStart_535685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535685 prefixEnd_535685 := by exact prefixLift 535685
  have htrace : WordTrace (prefixWord ++ tailWord_535685) baseStart_535685 baseEnd_535685 := by
    simpa [prefixWord, tailWord_535685, baseEnd_535685] using wordTrace_append hprefix tailTrace_535685
  have hstable : (prefixWord ++ tailWord_535685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535685).length < 2 ^ (prefixWord ++ tailWord_535685).sum := by decide
  have hdescent : baseEnd_535685 < baseStart_535685 := by decide
  rcases family_descends (prefixWord ++ tailWord_535685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535689 : List Nat := [1, 2, 1, 1, 4, 3, 3, 5]
def baseStart_535689 : Nat := 118140960795 + 535689 * 2 ^ 59
def prefixEnd_535689 : Nat := 4983230072969 + 3 ^ 40 * 535689 * 2
def baseEnd_535689 : Nat := 81501018763395510525605

theorem tailTrace_535689 : CollatzResearch.WordTrace tailWord_535689 prefixEnd_535689 81501018763395510525605 := by
  unfold tailWord_535689
  simp only [CollatzResearch.WordTrace]
  refine ⟨19538182956297716242546121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13025455304198477495030747 19538182956297716242546121)
  ·
    refine ⟨14653637217223287181909591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19538182956297716242546121 14653637217223287181909591)
    ·
      refine ⟨21980455825834930772864387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14653637217223287181909591 21980455825834930772864387)
      ·
        refine ⟨32970683738752396159296581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21980455825834930772864387 32970683738752396159296581)
        ·
          refine ⟨6182003201016074279868109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32970683738752396159296581 6182003201016074279868109)
          ·
            refine ⟨2318251200381027854950541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6182003201016074279868109 2318251200381027854950541)
            ·
              refine ⟨869344200142885445606453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2318251200381027854950541 869344200142885445606453)
              ·
                refine ⟨81501018763395510525605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 869344200142885445606453 81501018763395510525605)
                ·
                  rfl

theorem cell20_535689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 5].length) (baseStart_535689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535689 prefixEnd_535689 := by exact prefixLift 535689
  have htrace : WordTrace (prefixWord ++ tailWord_535689) baseStart_535689 baseEnd_535689 := by
    simpa [prefixWord, tailWord_535689, baseEnd_535689] using wordTrace_append hprefix tailTrace_535689
  have hstable : (prefixWord ++ tailWord_535689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535689).length < 2 ^ (prefixWord ++ tailWord_535689).sum := by decide
  have hdescent : baseEnd_535689 < baseStart_535689 := by decide
  rcases family_descends (prefixWord ++ tailWord_535689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535716 : List Nat := [2, 3, 1, 2, 3, 2, 2, 3, 2]
def baseStart_535716 : Nat := 118140960795 + 535716 * 2 ^ 59
def prefixEnd_535716 : Nat := 4983230072969 + 3 ^ 40 * 535716 * 2
def baseEnd_535716 : Nat := 244515379825894437676705

theorem tailTrace_535716 : CollatzResearch.WordTrace tailWord_535716 prefixEnd_535716 244515379825894437676705 := by
  unfold tailWord_535716
  simp only [CollatzResearch.WordTrace]
  refine ⟨9769583863599949926889501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13026111818133266569186001 9769583863599949926889501)
  ·
    refine ⟨3663593948849981222583563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9769583863599949926889501 3663593948849981222583563)
    ·
      refine ⟨5495390923274971833875345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3663593948849981222583563 5495390923274971833875345)
      ·
        refine ⟨4121543192456228875406509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5495390923274971833875345 4121543192456228875406509)
        ·
          refine ⟨1545578697171085828277441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4121543192456228875406509 1545578697171085828277441)
          ·
            refine ⟨1159184022878314371208081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1545578697171085828277441 1159184022878314371208081)
            ·
              refine ⟨869388017158735778406061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1159184022878314371208081 869388017158735778406061)
              ·
                refine ⟨326020506434525916902273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 869388017158735778406061 326020506434525916902273)
                ·
                  refine ⟨244515379825894437676705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326020506434525916902273 244515379825894437676705)
                  ·
                    rfl

theorem cell20_535716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_535716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535716 prefixEnd_535716 := by exact prefixLift 535716
  have htrace : WordTrace (prefixWord ++ tailWord_535716) baseStart_535716 baseEnd_535716 := by
    simpa [prefixWord, tailWord_535716, baseEnd_535716] using wordTrace_append hprefix tailTrace_535716
  have hstable : (prefixWord ++ tailWord_535716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535716).length < 2 ^ (prefixWord ++ tailWord_535716).sum := by decide
  have hdescent : baseEnd_535716 < baseStart_535716 := by decide
  rcases family_descends (prefixWord ++ tailWord_535716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535730 : List Nat := [3, 2, 1, 1, 1, 6, 1, 2, 3]
def baseStart_535730 : Nat := 118140960795 + 535730 * 2 ^ 59
def prefixEnd_535730 : Nat := 4983230072969 + 3 ^ 40 * 535730 * 2
def baseEnd_535730 : Nat := 244521769807372611209981

theorem tailTrace_535730 : CollatzResearch.WordTrace tailWord_535730 prefixEnd_535730 244521769807372611209981 := by
  unfold tailWord_535730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4884919587287295061197161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13026452232766120163192429 4884919587287295061197161)
  ·
    refine ⟨3663689690465471295897871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4884919587287295061197161 3663689690465471295897871)
    ·
      refine ⟨5495534535698206943846807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3663689690465471295897871 5495534535698206943846807)
      ·
        refine ⟨8243301803547310415770211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5495534535698206943846807 8243301803547310415770211)
        ·
          refine ⟨12364952705320965623655317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8243301803547310415770211 12364952705320965623655317)
          ·
            refine ⟨579607158061920263608843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12364952705320965623655317 579607158061920263608843)
            ·
              refine ⟨869410737092880395413265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579607158061920263608843 869410737092880395413265)
              ·
                refine ⟨652058052819660296559949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869410737092880395413265 652058052819660296559949)
                ·
                  refine ⟨244521769807372611209981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 652058052819660296559949 244521769807372611209981)
                  ·
                    rfl

theorem cell20_535730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_535730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535730 prefixEnd_535730 := by exact prefixLift 535730
  have htrace : WordTrace (prefixWord ++ tailWord_535730) baseStart_535730 baseEnd_535730 := by
    simpa [prefixWord, tailWord_535730, baseEnd_535730] using wordTrace_append hprefix tailTrace_535730
  have hstable : (prefixWord ++ tailWord_535730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535730).length < 2 ^ (prefixWord ++ tailWord_535730).sum := by decide
  have hdescent : baseEnd_535730 < baseStart_535730 := by decide
  rcases family_descends (prefixWord ++ tailWord_535730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535737 : List Nat := [1, 2, 1, 4, 1, 3, 2, 4, 2]
def baseStart_535737 : Nat := 118140960795 + 535737 * 2 ^ 59
def prefixEnd_535737 : Nat := 4983230072969 + 3 ^ 40 * 535737 * 2
def baseEnd_535737 : Nat := 244524964798111697976619

theorem tailTrace_535737 : CollatzResearch.WordTrace tailWord_535737 prefixEnd_535737 244524964798111697976619 := by
  unfold tailWord_535737
  simp only [CollatzResearch.WordTrace]
  refine ⟨19539933660123820440293465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13026622440082546960195643 19539933660123820440293465)
  ·
    refine ⟨14654950245092865330220099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19539933660123820440293465 14654950245092865330220099)
    ·
      refine ⟨21982425367639297995330149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14654950245092865330220099 21982425367639297995330149)
      ·
        refine ⟨4121704756432368374124403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21982425367639297995330149 4121704756432368374124403)
        ·
          refine ⟨6182557134648552561186605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4121704756432368374124403 6182557134648552561186605)
          ·
            refine ⟨2318458925493207210444977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6182557134648552561186605 2318458925493207210444977)
            ·
              refine ⟨1738844194119905407833733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2318458925493207210444977 1738844194119905407833733)
              ·
                refine ⟨326033286397482263968825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1738844194119905407833733 326033286397482263968825)
                ·
                  refine ⟨244524964798111697976619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326033286397482263968825 244524964798111697976619)
                  ·
                    rfl

theorem cell20_535737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 2].length) (baseStart_535737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535737 prefixEnd_535737 := by exact prefixLift 535737
  have htrace : WordTrace (prefixWord ++ tailWord_535737) baseStart_535737 baseEnd_535737 := by
    simpa [prefixWord, tailWord_535737, baseEnd_535737] using wordTrace_append hprefix tailTrace_535737
  have hstable : (prefixWord ++ tailWord_535737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535737).length < 2 ^ (prefixWord ++ tailWord_535737).sum := by decide
  have hdescent : baseEnd_535737 < baseStart_535737 := by decide
  rcases family_descends (prefixWord ++ tailWord_535737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
