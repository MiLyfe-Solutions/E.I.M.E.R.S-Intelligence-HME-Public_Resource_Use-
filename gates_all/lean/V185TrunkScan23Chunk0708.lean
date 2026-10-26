import V185TrunkScan23Chunk0707

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4185405 : List Nat := [1, 4, 1, 5, 1, 2, 1, 1, 7]
def baseStart_4185405 : Nat := 118140960795 + 4185405 * 2 ^ 59
def prefixEnd_4185405 : Nat := 4983230072969 + 3 ^ 40 * 4185405 * 2
def baseEnd_4185405 : Nat := 238791610970144701932131

theorem tailTrace_4185405 : CollatzResearch.WordTrace tailWord_4185405 prefixEnd_4185405 238791610970144701932131 := by
  unfold tailWord_4185405
  simp only [CollatzResearch.WordTrace]
  refine ⟨152654261401999970110157669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101769507601333313406771779 152654261401999970110157669)
  ·
    refine ⟨28622674012874994395654563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152654261401999970110157669 28622674012874994395654563)
    ·
      refine ⟨42934011019312491593481845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28622674012874994395654563 42934011019312491593481845)
      ·
        refine ⟨4025063533060546086888923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42934011019312491593481845 4025063533060546086888923)
        ·
          refine ⟨6037595299590819130333385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4025063533060546086888923 6037595299590819130333385)
          ·
            refine ⟨4528196474693114347750039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6037595299590819130333385 4528196474693114347750039)
            ·
              refine ⟨6792294712039671521625059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528196474693114347750039 6792294712039671521625059)
              ·
                refine ⟨10188442068059507282437589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6792294712039671521625059 10188442068059507282437589)
                ·
                  refine ⟨238791610970144701932131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10188442068059507282437589 238791610970144701932131)
                  ·
                    rfl

theorem cell23_4185405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_4185405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185405 prefixEnd_4185405 := by exact prefixLift 4185405
  have htrace : WordTrace (prefixWord ++ tailWord_4185405) baseStart_4185405 baseEnd_4185405 := by
    simpa [prefixWord, tailWord_4185405, baseEnd_4185405] using wordTrace_append hprefix tailTrace_4185405
  have hstable : (prefixWord ++ tailWord_4185405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185405).length < 2 ^ (prefixWord ++ tailWord_4185405).sum := by decide
  have hdescent : baseEnd_4185405 < baseStart_4185405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185441 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 1, 4, 3]
def baseStart_4185441 : Nat := 118140960795 + 4185441 * 2 ^ 59
def prefixEnd_4185441 : Nat := 4983230072969 + 3 ^ 40 * 4185441 * 2
def baseEnd_4185441 : Nat := 2149142984034864176539013

theorem tailTrace_4185441 : CollatzResearch.WordTrace tailWord_4185441 prefixEnd_4185441 2149142984034864176539013 := by
  unfold tailWord_4185441
  simp only [CollatzResearch.WordTrace]
  refine ⟨152655574429869548258468177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101770382953246365505645451 152655574429869548258468177)
  ·
    refine ⟨114491680822402161193851133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152655574429869548258468177 114491680822402161193851133)
    ·
      refine ⟨42934380308400810447694175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114491680822402161193851133 42934380308400810447694175)
      ·
        refine ⟨64401570462601215671541263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42934380308400810447694175 64401570462601215671541263)
        ·
          refine ⟨96602355693901823507311895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64401570462601215671541263 96602355693901823507311895)
          ·
            refine ⟨144903533540852735260967843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96602355693901823507311895 144903533540852735260967843)
            ·
              refine ⟨217355300311279102891451765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144903533540852735260967843 217355300311279102891451765)
              ·
                refine ⟨20377059404182415896073603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217355300311279102891451765 20377059404182415896073603)
                ·
                  refine ⟨30565589106273623844110405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20377059404182415896073603 30565589106273623844110405)
                  ·
                    refine ⟨5731047957426304470770701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30565589106273623844110405 5731047957426304470770701)
                    ·
                      refine ⟨2149142984034864176539013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5731047957426304470770701 2149142984034864176539013)
                      ·
                        rfl

theorem cell23_4185441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_4185441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185441 prefixEnd_4185441 := by exact prefixLift 4185441
  have htrace : WordTrace (prefixWord ++ tailWord_4185441) baseStart_4185441 baseEnd_4185441 := by
    simpa [prefixWord, tailWord_4185441, baseEnd_4185441] using wordTrace_append hprefix tailTrace_4185441
  have hstable : (prefixWord ++ tailWord_4185441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185441).length < 2 ^ (prefixWord ++ tailWord_4185441).sum := by decide
  have hdescent : baseEnd_4185441 < baseStart_4185441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185458 : List Nat := [3, 2, 1, 2, 1, 2, 1, 4, 2, 2, 3]
def baseStart_4185458 : Nat := 118140960795 + 4185458 * 2 ^ 59
def prefixEnd_4185458 : Nat := 4983230072969 + 3 ^ 40 * 4185458 * 2
def baseEnd_4185458 : Nat := 2149151713205990610026435

theorem tailTrace_4185458 : CollatzResearch.WordTrace tailWord_4185458 prefixEnd_4185458 2149151713205990610026435 := by
  unfold tailWord_4185458
  simp only [CollatzResearch.WordTrace]
  refine ⟨38164048617701990040459257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101770796313871973441224685 38164048617701990040459257)
  ·
    refine ⟨28623036463276492530344443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38164048617701990040459257 28623036463276492530344443)
    ·
      refine ⟨42934554694914738795516665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28623036463276492530344443 42934554694914738795516665)
      ·
        refine ⟨32200916021186054096637499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42934554694914738795516665 32200916021186054096637499)
        ·
          refine ⟨48301374031779081144956249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32200916021186054096637499 48301374031779081144956249)
          ·
            refine ⟨36226030523834310858717187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48301374031779081144956249 36226030523834310858717187)
            ·
              refine ⟨54339045785751466288075781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36226030523834310858717187 54339045785751466288075781)
              ·
                refine ⟨10188571084828399929014209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54339045785751466288075781 10188571084828399929014209)
                ·
                  refine ⟨7641428313621299946760657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10188571084828399929014209 7641428313621299946760657)
                  ·
                    refine ⟨5731071235215974960070493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7641428313621299946760657 5731071235215974960070493)
                    ·
                      refine ⟨2149151713205990610026435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5731071235215974960070493 2149151713205990610026435)
                      ·
                        rfl

theorem cell23_4185458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_4185458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185458 prefixEnd_4185458 := by exact prefixLift 4185458
  have htrace : WordTrace (prefixWord ++ tailWord_4185458) baseStart_4185458 baseEnd_4185458 := by
    simpa [prefixWord, tailWord_4185458, baseEnd_4185458] using wordTrace_append hprefix tailTrace_4185458
  have hstable : (prefixWord ++ tailWord_4185458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185458).length < 2 ^ (prefixWord ++ tailWord_4185458).sum := by decide
  have hdescent : baseEnd_4185458 < baseStart_4185458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185492 : List Nat := [2, 4, 2, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_4185492 : Nat := 118140960795 + 4185492 * 2 ^ 59
def prefixEnd_4185492 : Nat := 4983230072969 + 3 ^ 40 * 4185492 * 2
def baseEnd_4185492 : Nat := 2149169171548243477001279

theorem tailTrace_4185492 : CollatzResearch.WordTrace tailWord_4185492 prefixEnd_4185492 2149169171548243477001279 := by
  unfold tailWord_4185492
  simp only [CollatzResearch.WordTrace]
  refine ⟨76328717276342391984287365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101771623035123189312383153 76328717276342391984287365)
  ·
    refine ⟨14311634489314198497053881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76328717276342391984287365 14311634489314198497053881)
    ·
      refine ⟨10733725866985648872790411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14311634489314198497053881 10733725866985648872790411)
      ·
        refine ⟨16100588800478473309185617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10733725866985648872790411 16100588800478473309185617)
        ·
          refine ⟨12075441600358854981889213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16100588800478473309185617 12075441600358854981889213)
          ·
            refine ⟨4528290600134570618208455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12075441600358854981889213 4528290600134570618208455)
            ·
              refine ⟨6792435900201855927312683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528290600134570618208455 6792435900201855927312683)
              ·
                refine ⟨10188653850302783890969025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6792435900201855927312683 10188653850302783890969025)
                ·
                  refine ⟨7641490387727087918226769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10188653850302783890969025 7641490387727087918226769)
                  ·
                    refine ⟨5731117790795315938670077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7641490387727087918226769 5731117790795315938670077)
                    ·
                      refine ⟨2149169171548243477001279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5731117790795315938670077 2149169171548243477001279)
                      ·
                        rfl

theorem cell23_4185492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_4185492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185492 prefixEnd_4185492 := by exact prefixLift 4185492
  have htrace : WordTrace (prefixWord ++ tailWord_4185492) baseStart_4185492 baseEnd_4185492 := by
    simpa [prefixWord, tailWord_4185492, baseEnd_4185492] using wordTrace_append hprefix tailTrace_4185492
  have hstable : (prefixWord ++ tailWord_4185492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185492).length < 2 ^ (prefixWord ++ tailWord_4185492).sum := by decide
  have hdescent : baseEnd_4185492 < baseStart_4185492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185512 : List Nat := [2, 1, 6, 1, 2, 2, 1, 2, 6]
def baseStart_4185512 : Nat := 118140960795 + 4185512 * 2 ^ 59
def prefixEnd_4185512 : Nat := 4983230072969 + 3 ^ 40 * 4185512 * 2
def baseEnd_4185512 : Nat := 238797715684592599861243

theorem tailTrace_4185512 : CollatzResearch.WordTrace tailWord_4185512 prefixEnd_4185512 238797715684592599861243 := by
  unfold tailWord_4185512
  simp only [CollatzResearch.WordTrace]
  refine ⟨76329082006306163692151395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101772109341741551589535193 76329082006306163692151395)
  ·
    refine ⟨114493623009459245538227093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76329082006306163692151395 114493623009459245538227093)
    ·
      refine ⟨5366888578568402134604395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 114493623009459245538227093 5366888578568402134604395)
      ·
        refine ⟨8050332867852603201906593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5366888578568402134604395 8050332867852603201906593)
        ·
          refine ⟨6037749650889452401429945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8050332867852603201906593 6037749650889452401429945)
          ·
            refine ⟨4528312238167089301072459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6037749650889452401429945 4528312238167089301072459)
            ·
              refine ⟨6792468357250633951608689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528312238167089301072459 6792468357250633951608689)
              ·
                refine ⟨5094351267937975463706517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6792468357250633951608689 5094351267937975463706517)
                ·
                  refine ⟨238797715684592599861243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5094351267937975463706517 238797715684592599861243)
                  ·
                    rfl

theorem cell23_4185512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 6].length) (baseStart_4185512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185512 prefixEnd_4185512 := by exact prefixLift 4185512
  have htrace : WordTrace (prefixWord ++ tailWord_4185512) baseStart_4185512 baseEnd_4185512 := by
    simpa [prefixWord, tailWord_4185512, baseEnd_4185512] using wordTrace_append hprefix tailTrace_4185512
  have hstable : (prefixWord ++ tailWord_4185512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185512).length < 2 ^ (prefixWord ++ tailWord_4185512).sum := by decide
  have hdescent : baseEnd_4185512 < baseStart_4185512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185556 : List Nat := [2, 4, 1, 2, 3, 2, 1, 3, 1, 1, 3]
def baseStart_4185556 : Nat := 118140960795 + 4185556 * 2 ^ 59
def prefixEnd_4185556 : Nat := 4983230072969 + 3 ^ 40 * 4185556 * 2
def baseEnd_4185556 : Nat := 2149202034310131226600985

theorem tailTrace_4185556 : CollatzResearch.WordTrace tailWord_4185556 prefixEnd_4185556 2149202034310131226600985 := by
  unfold tailWord_4185556
  simp only [CollatzResearch.WordTrace]
  refine ⟨76329884412226461449452261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101773179216301948599269681 76329884412226461449452261)
  ·
    refine ⟨14311853327292461521772299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76329884412226461449452261 14311853327292461521772299)
    ·
      refine ⟨21467779990938692282658449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14311853327292461521772299 21467779990938692282658449)
      ·
        refine ⟨16100834993204019211993837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21467779990938692282658449 16100834993204019211993837)
        ·
          refine ⟨6037813122451507204497689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16100834993204019211993837 6037813122451507204497689)
          ·
            refine ⟨4528359841838630403373267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6037813122451507204497689 4528359841838630403373267)
            ·
              refine ⟨6792539762757945605059901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528359841838630403373267 6792539762757945605059901)
              ·
                refine ⟨2547202411034229601897463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6792539762757945605059901 2547202411034229601897463)
                ·
                  refine ⟨3820803616551344402846195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2547202411034229601897463 3820803616551344402846195)
                  ·
                    refine ⟨5731205424827016604269293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3820803616551344402846195 5731205424827016604269293)
                    ·
                      refine ⟨2149202034310131226600985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5731205424827016604269293 2149202034310131226600985)
                      ·
                        rfl

theorem cell23_4185556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_4185556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185556 prefixEnd_4185556 := by exact prefixLift 4185556
  have htrace : WordTrace (prefixWord ++ tailWord_4185556) baseStart_4185556 baseEnd_4185556 := by
    simpa [prefixWord, tailWord_4185556, baseEnd_4185556] using wordTrace_append hprefix tailTrace_4185556
  have hstable : (prefixWord ++ tailWord_4185556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185556).length < 2 ^ (prefixWord ++ tailWord_4185556).sum := by decide
  have hdescent : baseEnd_4185556 < baseStart_4185556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185565 : List Nat := [1, 4, 3, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_4185565 : Nat := 118140960795 + 4185565 * 2 ^ 59
def prefixEnd_4185565 : Nat := 4983230072969 + 3 ^ 40 * 4185565 * 2
def baseEnd_4185565 : Nat := 2149206655636021691388443

theorem tailTrace_4185565 : CollatzResearch.WordTrace tailWord_4185565 prefixEnd_4185565 2149206655636021691388443 := by
  unfold tailWord_4185565
  simp only [CollatzResearch.WordTrace]
  refine ⟨152660097081420317435982149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101773398054280211623988099 152660097081420317435982149)
  ·
    refine ⟨28623768202766309519246653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152660097081420317435982149 28623768202766309519246653)
    ·
      refine ⟨10733913076037366069717495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28623768202766309519246653 10733913076037366069717495)
      ·
        refine ⟨16100869614056049104576243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10733913076037366069717495 16100869614056049104576243)
        ·
          refine ⟨24151304421084073656864365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16100869614056049104576243 24151304421084073656864365)
          ·
            refine ⟨9056739157906527621324137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24151304421084073656864365 9056739157906527621324137)
            ·
              refine ⟨6792554368429895715993103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9056739157906527621324137 6792554368429895715993103)
              ·
                refine ⟨10188831552644843573989655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6792554368429895715993103 10188831552644843573989655)
                ·
                  refine ⟨15283247328967265360984483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10188831552644843573989655 15283247328967265360984483)
                  ·
                    refine ⟨22924870993450898041476725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15283247328967265360984483 22924870993450898041476725)
                    ·
                      refine ⟨2149206655636021691388443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22924870993450898041476725 2149206655636021691388443)
                      ·
                        rfl

theorem cell23_4185565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_4185565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185565 prefixEnd_4185565 := by exact prefixLift 4185565
  have htrace : WordTrace (prefixWord ++ tailWord_4185565) baseStart_4185565 baseEnd_4185565 := by
    simpa [prefixWord, tailWord_4185565, baseEnd_4185565] using wordTrace_append hprefix tailTrace_4185565
  have hstable : (prefixWord ++ tailWord_4185565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185565).length < 2 ^ (prefixWord ++ tailWord_4185565).sum := by decide
  have hdescent : baseEnd_4185565 < baseStart_4185565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185589 : List Nat := [1, 3, 5, 1, 1, 1, 4, 1, 2, 4]
def baseStart_4185589 : Nat := 118140960795 + 4185589 * 2 ^ 59
def prefixEnd_4185589 : Nat := 4983230072969 + 3 ^ 40 * 4185589 * 2
def baseEnd_4185589 : Nat := 716406326390576532496111

theorem tailTrace_4185589 : CollatzResearch.WordTrace tailWord_4185589 prefixEnd_4185589 716406326390576532496111 := by
  unfold tailWord_4185589
  simp only [CollatzResearch.WordTrace]
  refine ⟨152660972433333369534855821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101773981622222246356570547 152660972433333369534855821)
  ·
    refine ⟨57247864662500013575570933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152660972433333369534855821 57247864662500013575570933)
    ·
      refine ⟨5366987312109376272709775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57247864662500013575570933 5366987312109376272709775)
      ·
        refine ⟨8050480968164064409064663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5366987312109376272709775 8050480968164064409064663)
        ·
          refine ⟨12075721452246096613596995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8050480968164064409064663 12075721452246096613596995)
          ·
            refine ⟨18113582178369144920395493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12075721452246096613596995 18113582178369144920395493)
            ·
              refine ⟨3396296658444214672574155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18113582178369144920395493 3396296658444214672574155)
              ·
                refine ⟨5094444987666322008861233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3396296658444214672574155 5094444987666322008861233)
                ·
                  refine ⟨3820833740749741506645925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5094444987666322008861233 3820833740749741506645925)
                  ·
                    refine ⟨716406326390576532496111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3820833740749741506645925 716406326390576532496111)
                    ·
                      rfl

theorem cell23_4185589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_4185589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185589 prefixEnd_4185589 := by exact prefixLift 4185589
  have htrace : WordTrace (prefixWord ++ tailWord_4185589) baseStart_4185589 baseEnd_4185589 := by
    simpa [prefixWord, tailWord_4185589, baseEnd_4185589] using wordTrace_append hprefix tailTrace_4185589
  have hstable : (prefixWord ++ tailWord_4185589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185589).length < 2 ^ (prefixWord ++ tailWord_4185589).sum := by decide
  have hdescent : baseEnd_4185589 < baseStart_4185589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185591 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 5]
def baseStart_4185591 : Nat := 118140960795 + 4185591 * 2 ^ 59
def prefixEnd_4185591 : Nat := 4983230072969 + 3 ^ 40 * 4185591 * 2
def baseEnd_4185591 : Nat := 2149220006133038589663323

theorem tailTrace_4185591 : CollatzResearch.WordTrace tailWord_4185591 prefixEnd_4185591 2149220006133038589663323 := by
  unfold tailWord_4185591
  simp only [CollatzResearch.WordTrace]
  refine ⟨152661045379326123876428627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101774030252884082584285751 152661045379326123876428627)
  ·
    refine ⟨228991568068989185814642941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152661045379326123876428627 228991568068989185814642941)
    ·
      refine ⟨85871838025870944680491103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228991568068989185814642941 85871838025870944680491103)
      ·
        refine ⟨128807757038806417020736655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85871838025870944680491103 128807757038806417020736655)
        ·
          refine ⟨193211635558209625531104983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128807757038806417020736655 193211635558209625531104983)
          ·
            refine ⟨289817453337314438296657475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193211635558209625531104983 289817453337314438296657475)
            ·
              refine ⟨434726180005971657444986213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289817453337314438296657475 434726180005971657444986213)
              ·
                refine ⟨81511158751119685770934915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 434726180005971657444986213 81511158751119685770934915)
                ·
                  refine ⟨122266738126679528656402373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81511158751119685770934915 122266738126679528656402373)
                  ·
                    refine ⟨22925013398752411623075445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122266738126679528656402373 22925013398752411623075445)
                    ·
                      refine ⟨2149220006133038589663323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22925013398752411623075445 2149220006133038589663323)
                      ·
                        rfl

theorem cell23_4185591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_4185591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185591 prefixEnd_4185591 := by exact prefixLift 4185591
  have htrace : WordTrace (prefixWord ++ tailWord_4185591) baseStart_4185591 baseEnd_4185591 := by
    simpa [prefixWord, tailWord_4185591, baseEnd_4185591] using wordTrace_append hprefix tailTrace_4185591
  have hstable : (prefixWord ++ tailWord_4185591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185591).length < 2 ^ (prefixWord ++ tailWord_4185591).sum := by decide
  have hdescent : baseEnd_4185591 < baseStart_4185591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185595 : List Nat := [1, 1, 1, 1, 1, 3, 2, 7, 2, 1, 3]
def baseStart_4185595 : Nat := 118140960795 + 4185595 * 2 ^ 59
def prefixEnd_4185595 : Nat := 4983230072969 + 3 ^ 40 * 4185595 * 2
def baseEnd_4185595 : Nat := 2149222060055656574013305

theorem tailTrace_4185595 : CollatzResearch.WordTrace tailWord_4185595 prefixEnd_4185595 2149222060055656574013305 := by
  unfold tailWord_4185595
  simp only [CollatzResearch.WordTrace]
  refine ⟨152661191271311632559574239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101774127514207755039716159 152661191271311632559574239)
  ·
    refine ⟨228991786906967448839361359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152661191271311632559574239 228991786906967448839361359)
    ·
      refine ⟨343487680360451173259042039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228991786906967448839361359 343487680360451173259042039)
      ·
        refine ⟨515231520540676759888563059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343487680360451173259042039 515231520540676759888563059)
        ·
          refine ⟨772847280811015139832844589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515231520540676759888563059 772847280811015139832844589)
          ·
            refine ⟨289817730304130677437316721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 772847280811015139832844589 289817730304130677437316721)
            ·
              refine ⟨217363297728098008077987541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289817730304130677437316721 217363297728098008077987541)
              ·
                refine ⟨5094452290502297064327833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 217363297728098008077987541 5094452290502297064327833)
                ·
                  refine ⟨3820839217876722798245875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5094452290502297064327833 3820839217876722798245875)
                  ·
                    refine ⟨5731258826815084197368813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3820839217876722798245875 5731258826815084197368813)
                    ·
                      refine ⟨2149222060055656574013305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5731258826815084197368813 2149222060055656574013305)
                      ·
                        rfl

theorem cell23_4185595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 1, 3].length) (baseStart_4185595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185595 prefixEnd_4185595 := by exact prefixLift 4185595
  have htrace : WordTrace (prefixWord ++ tailWord_4185595) baseStart_4185595 baseEnd_4185595 := by
    simpa [prefixWord, tailWord_4185595, baseEnd_4185595] using wordTrace_append hprefix tailTrace_4185595
  have hstable : (prefixWord ++ tailWord_4185595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185595).length < 2 ^ (prefixWord ++ tailWord_4185595).sum := by decide
  have hdescent : baseEnd_4185595 < baseStart_4185595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185628 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 2, 6]
def baseStart_4185628 : Nat := 118140960795 + 4185628 * 2 ^ 59
def prefixEnd_4185628 : Nat := 4983230072969 + 3 ^ 40 * 4185628 * 2
def baseEnd_4185628 : Nat := 716413001639084981633551

theorem tailTrace_4185628 : CollatzResearch.WordTrace tailWord_4185628 prefixEnd_4185628 716413001639084981633551 := by
  unfold tailWord_4185628
  simp only [CollatzResearch.WordTrace]
  refine ⟨76331197440096039597762769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101774929920128052797017025 76331197440096039597762769)
  ·
    refine ⟨57248398080072029698322077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76331197440096039597762769 57248398080072029698322077)
    ·
      refine ⟨21468149280027011136870779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57248398080072029698322077 21468149280027011136870779)
      ·
        refine ⟨32202223920040516705306169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21468149280027011136870779 32202223920040516705306169)
        ·
          refine ⟨24151667940030387528979627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32202223920040516705306169 24151667940030387528979627)
          ·
            refine ⟨36227501910045581293469441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24151667940030387528979627 36227501910045581293469441)
            ·
              refine ⟨27170626432534185970102081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36227501910045581293469441 27170626432534185970102081)
              ·
                refine ⟨20377969824400639477576561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27170626432534185970102081 20377969824400639477576561)
                ·
                  refine ⟨15283477368300479608182421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20377969824400639477576561 15283477368300479608182421)
                  ·
                    refine ⟨716413001639084981633551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15283477368300479608182421 716413001639084981633551)
                    ·
                      rfl

theorem cell23_4185628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_4185628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185628 prefixEnd_4185628 := by exact prefixLift 4185628
  have htrace : WordTrace (prefixWord ++ tailWord_4185628) baseStart_4185628 baseEnd_4185628 := by
    simpa [prefixWord, tailWord_4185628, baseEnd_4185628] using wordTrace_append hprefix tailTrace_4185628
  have hstable : (prefixWord ++ tailWord_4185628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185628).length < 2 ^ (prefixWord ++ tailWord_4185628).sum := by decide
  have hdescent : baseEnd_4185628 < baseStart_4185628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185658 : List Nat := [3, 1, 1, 1, 3, 2, 3, 2, 7]
def baseStart_4185658 : Nat := 118140960795 + 4185658 * 2 ^ 59
def prefixEnd_4185658 : Nat := 4983230072969 + 3 ^ 40 * 4185658 * 2
def baseEnd_4185658 : Nat := 238806045481876647502835

theorem tailTrace_4185658 : CollatzResearch.WordTrace tailWord_4185658 prefixEnd_4185658 238806045481876647502835 := by
  unfold tailWord_4185658
  simp only [CollatzResearch.WordTrace]
  refine ⟨38165872267520848579779407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101775659380055596212745085 38165872267520848579779407)
  ·
    refine ⟨57248808401281272869669111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38165872267520848579779407 57248808401281272869669111)
    ·
      refine ⟨85873212601921909304503667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57248808401281272869669111 85873212601921909304503667)
      ·
        refine ⟨128809818902882863956755501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85873212601921909304503667 128809818902882863956755501)
        ·
          refine ⟨48303682088581073983783313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128809818902882863956755501 48303682088581073983783313)
          ·
            refine ⟨36227761566435805487837485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48303682088581073983783313 36227761566435805487837485)
            ·
              refine ⟨13585410587413427057939057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36227761566435805487837485 13585410587413427057939057)
              ·
                refine ⟨10189057940560070293454293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13585410587413427057939057 10189057940560070293454293)
                ·
                  refine ⟨238806045481876647502835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10189057940560070293454293 238806045481876647502835)
                  ·
                    rfl

theorem cell23_4185658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 7].length) (baseStart_4185658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185658 prefixEnd_4185658 := by exact prefixLift 4185658
  have htrace : WordTrace (prefixWord ++ tailWord_4185658) baseStart_4185658 baseEnd_4185658 := by
    simpa [prefixWord, tailWord_4185658, baseEnd_4185658] using wordTrace_append hprefix tailTrace_4185658
  have hstable : (prefixWord ++ tailWord_4185658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185658).length < 2 ^ (prefixWord ++ tailWord_4185658).sum := by decide
  have hdescent : baseEnd_4185658 < baseStart_4185658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185688 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 4, 5]
def baseStart_4185688 : Nat := 118140960795 + 4185688 * 2 ^ 59
def prefixEnd_4185688 : Nat := 4983230072969 + 3 ^ 40 * 4185688 * 2
def baseEnd_4185688 : Nat := 716423271252174903383459

theorem tailTrace_4185688 : CollatzResearch.WordTrace tailWord_4185688 prefixEnd_4185688 716423271252174903383459 := by
  unfold tailWord_4185688
  simp only [CollatzResearch.WordTrace]
  refine ⟨76332291629987354721354859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101776388839983139628473145 76332291629987354721354859)
  ·
    refine ⟨114498437444981032082032289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76332291629987354721354859 114498437444981032082032289)
    ·
      refine ⟨85873828083735774061524217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114498437444981032082032289 85873828083735774061524217)
      ·
        refine ⟨64405371062801830546143163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85873828083735774061524217 64405371062801830546143163)
        ·
          refine ⟨96608056594202745819214745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64405371062801830546143163 96608056594202745819214745)
          ·
            refine ⟨72456042445652059364411059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96608056594202745819214745 72456042445652059364411059)
            ·
              refine ⟨108684063668478089046616589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72456042445652059364411059 108684063668478089046616589)
              ·
                refine ⟨40756523875679283392481221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108684063668478089046616589 40756523875679283392481221)
                ·
                  refine ⟨7641848226689865636090229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40756523875679283392481221 7641848226689865636090229)
                  ·
                    refine ⟨716423271252174903383459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7641848226689865636090229 716423271252174903383459)
                    ·
                      rfl

theorem cell23_4185688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_4185688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185688 prefixEnd_4185688 := by exact prefixLift 4185688
  have htrace : WordTrace (prefixWord ++ tailWord_4185688) baseStart_4185688 baseEnd_4185688 := by
    simpa [prefixWord, tailWord_4185688, baseEnd_4185688] using wordTrace_append hprefix tailTrace_4185688
  have hstable : (prefixWord ++ tailWord_4185688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185688).length < 2 ^ (prefixWord ++ tailWord_4185688).sum := by decide
  have hdescent : baseEnd_4185688 < baseStart_4185688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185692 : List Nat := [2, 2, 4, 1, 2, 1, 2, 4, 5]
def baseStart_4185692 : Nat := 118140960795 + 4185692 * 2 ^ 59
def prefixEnd_4185692 : Nat := 4983230072969 + 3 ^ 40 * 4185692 * 2
def baseEnd_4185692 : Nat := 238807985297682521611151

theorem tailTrace_4185692 : CollatzResearch.WordTrace tailWord_4185692 prefixEnd_4185692 238807985297682521611151 := by
  unfold tailWord_4185692
  simp only [CollatzResearch.WordTrace]
  refine ⟨76332364575980109062927665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101776486101306812083903553 76332364575980109062927665)
  ·
    refine ⟨57249273431985081797195749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76332364575980109062927665 57249273431985081797195749)
    ·
      refine ⟨10734238768497202836974203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57249273431985081797195749 10734238768497202836974203)
      ·
        refine ⟨16101358152745804255461305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10734238768497202836974203 16101358152745804255461305)
        ·
          refine ⟨12076018614559353191595979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16101358152745804255461305 12076018614559353191595979)
          ·
            refine ⟨18114027921839029787393969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12076018614559353191595979 18114027921839029787393969)
            ·
              refine ⟨13585520941379272340545477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18114027921839029787393969 13585520941379272340545477)
              ·
                refine ⟨2547285176508613563852277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13585520941379272340545477 2547285176508613563852277)
                ·
                  refine ⟨238807985297682521611151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2547285176508613563852277 238807985297682521611151)
                  ·
                    rfl

theorem cell23_4185692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 5].length) (baseStart_4185692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185692 prefixEnd_4185692 := by exact prefixLift 4185692
  have htrace : WordTrace (prefixWord ++ tailWord_4185692) baseStart_4185692 baseEnd_4185692 := by
    simpa [prefixWord, tailWord_4185692, baseEnd_4185692] using wordTrace_append hprefix tailTrace_4185692
  have hstable : (prefixWord ++ tailWord_4185692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185692).length < 2 ^ (prefixWord ++ tailWord_4185692).sum := by decide
  have hdescent : baseEnd_4185692 < baseStart_4185692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185725 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_4185725 : Nat := 118140960795 + 4185725 * 2 ^ 59
def prefixEnd_4185725 : Nat := 4983230072969 + 3 ^ 40 * 4185725 * 2
def baseEnd_4185725 : Nat := 2149288812540741065387707

theorem tailTrace_4185725 : CollatzResearch.WordTrace tailWord_4185725 prefixEnd_4185725 2149288812540741065387707 := by
  unfold tailWord_4185725
  simp only [CollatzResearch.WordTrace]
  refine ⟨152665932760840664761806629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101777288507227109841204419 152665932760840664761806629)
  ·
    refine ⟨28624862392657624642838743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152665932760840664761806629 28624862392657624642838743)
    ·
      refine ⟨42937293588986436964258115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28624862392657624642838743 42937293588986436964258115)
      ·
        refine ⟨64405940383479655446387173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42937293588986436964258115 64405940383479655446387173)
        ·
          refine ⟨12076113821902435396197595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64405940383479655446387173 12076113821902435396197595)
          ·
            refine ⟨18114170732853653094296393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12076113821902435396197595 18114170732853653094296393)
            ·
              refine ⟨13585628049640239820722295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18114170732853653094296393 13585628049640239820722295)
              ·
                refine ⟨20378442074460359731083443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13585628049640239820722295 20378442074460359731083443)
                ·
                  refine ⟨30567663111690539596625165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20378442074460359731083443 30567663111690539596625165)
                  ·
                    refine ⟨11462873666883952348734437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30567663111690539596625165 11462873666883952348734437)
                    ·
                      refine ⟨2149288812540741065387707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11462873666883952348734437 2149288812540741065387707)
                      ·
                        rfl

theorem cell23_4185725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_4185725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185725 prefixEnd_4185725 := by exact prefixLift 4185725
  have htrace : WordTrace (prefixWord ++ tailWord_4185725) baseStart_4185725 baseEnd_4185725 := by
    simpa [prefixWord, tailWord_4185725, baseEnd_4185725] using wordTrace_append hprefix tailTrace_4185725
  have hstable : (prefixWord ++ tailWord_4185725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185725).length < 2 ^ (prefixWord ++ tailWord_4185725).sum := by decide
  have hdescent : baseEnd_4185725 < baseStart_4185725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185742 : List Nat := [4, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_4185742 : Nat := 118140960795 + 4185742 * 2 ^ 59
def prefixEnd_4185742 : Nat := 4983230072969 + 3 ^ 40 * 4185742 * 2
def baseEnd_4185742 : Nat := 2149297541711867498875129

theorem tailTrace_4185742 : CollatzResearch.WordTrace tailWord_4185742 prefixEnd_4185742 2149297541711867498875129 := by
  unfold tailWord_4185742
  simp only [CollatzResearch.WordTrace]
  refine ⟨19083319100222384583146935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101777701867852717776783653 19083319100222384583146935)
  ·
    refine ⟨28624978650333576874720403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19083319100222384583146935 28624978650333576874720403)
    ·
      refine ⟨42937467975500365312080605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28624978650333576874720403 42937467975500365312080605)
      ·
        refine ⟨16101550490812636992030227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42937467975500365312080605 16101550490812636992030227)
        ·
          refine ⟨24152325736218955488045341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16101550490812636992030227 24152325736218955488045341)
          ·
            refine ⟨9057122151082108308017003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24152325736218955488045341 9057122151082108308017003)
            ·
              refine ⟨13585683226623162462025505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9057122151082108308017003 13585683226623162462025505)
              ·
                refine ⟨10189262419967371846519129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13585683226623162462025505 10189262419967371846519129)
                ·
                  refine ⟨7641946814975528884889347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10189262419967371846519129 7641946814975528884889347)
                  ·
                    refine ⟨11462920222463293327334021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7641946814975528884889347 11462920222463293327334021)
                    ·
                      refine ⟨2149297541711867498875129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11462920222463293327334021 2149297541711867498875129)
                      ·
                        rfl

theorem cell23_4185742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_4185742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185742 prefixEnd_4185742 := by exact prefixLift 4185742
  have htrace : WordTrace (prefixWord ++ tailWord_4185742) baseStart_4185742 baseEnd_4185742 := by
    simpa [prefixWord, tailWord_4185742, baseEnd_4185742] using wordTrace_append hprefix tailTrace_4185742
  have hstable : (prefixWord ++ tailWord_4185742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185742).length < 2 ^ (prefixWord ++ tailWord_4185742).sum := by decide
  have hdescent : baseEnd_4185742 < baseStart_4185742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185752 : List Nat := [2, 1, 2, 4, 1, 2, 3, 1, 3, 4]
def baseStart_4185752 : Nat := 118140960795 + 4185752 * 2 ^ 59
def prefixEnd_4185752 : Nat := 4983230072969 + 3 ^ 40 * 4185752 * 2
def baseEnd_4185752 : Nat := 716434225506137486583361

theorem tailTrace_4185752 : CollatzResearch.WordTrace tailWord_4185752 prefixEnd_4185752 716434225506137486583361 := by
  unfold tailWord_4185752
  simp only [CollatzResearch.WordTrace]
  refine ⟨76333458765871424186519755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101777945021161898915359673 76333458765871424186519755)
  ·
    refine ⟨114500188148807136279779633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76333458765871424186519755 114500188148807136279779633)
    ·
      refine ⟨85875141111605352209834725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114500188148807136279779633 85875141111605352209834725)
      ·
        refine ⟨16101588958426003539344011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85875141111605352209834725 16101588958426003539344011)
        ·
          refine ⟨24152383437639005309016017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16101588958426003539344011 24152383437639005309016017)
          ·
            refine ⟨18114287578229253981762013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24152383437639005309016017 18114287578229253981762013)
            ·
              refine ⟨6792857841835970243160755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18114287578229253981762013 6792857841835970243160755)
              ·
                refine ⟨10189286762753955364741133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6792857841835970243160755 10189286762753955364741133)
                ·
                  refine ⟨3820982536032733261777925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10189286762753955364741133 3820982536032733261777925)
                  ·
                    refine ⟨716434225506137486583361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3820982536032733261777925 716434225506137486583361)
                    ·
                      rfl

theorem cell23_4185752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_4185752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185752 prefixEnd_4185752 := by exact prefixLift 4185752
  have htrace : WordTrace (prefixWord ++ tailWord_4185752) baseStart_4185752 baseEnd_4185752 := by
    simpa [prefixWord, tailWord_4185752, baseEnd_4185752] using wordTrace_append hprefix tailTrace_4185752
  have hstable : (prefixWord ++ tailWord_4185752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185752).length < 2 ^ (prefixWord ++ tailWord_4185752).sum := by decide
  have hdescent : baseEnd_4185752 < baseStart_4185752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185812 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_4185812 : Nat := 118140960795 + 4185812 * 2 ^ 59
def prefixEnd_4185812 : Nat := 4983230072969 + 3 ^ 40 * 4185812 * 2
def baseEnd_4185812 : Nat := 716444495119227408333269

theorem tailTrace_4185812 : CollatzResearch.WordTrace tailWord_4185812 prefixEnd_4185812 716444495119227408333269 := by
  unfold tailWord_4185812
  simp only [CollatzResearch.WordTrace]
  refine ⟨76334552955762739310111845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101779403941016985746815793 76334552955762739310111845)
  ·
    refine ⟨14312728679205513620645971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76334552955762739310111845 14312728679205513620645971)
    ·
      refine ⟨21469093018808270430968957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14312728679205513620645971 21469093018808270430968957)
      ·
        refine ⟨8050909882053101411613359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21469093018808270430968957 8050909882053101411613359)
        ·
          refine ⟨12076364823079652117420039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8050909882053101411613359 12076364823079652117420039)
          ·
            refine ⟨18114547234619478176130059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12076364823079652117420039 18114547234619478176130059)
            ·
              refine ⟨27171820851929217264195089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18114547234619478176130059 27171820851929217264195089)
              ·
                refine ⟨20378865638946912948146317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27171820851929217264195089 20378865638946912948146317)
                ·
                  refine ⟨7642074614605092355554869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20378865638946912948146317 7642074614605092355554869)
                  ·
                    refine ⟨716444495119227408333269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7642074614605092355554869 716444495119227408333269)
                    ·
                      rfl

theorem cell23_4185812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_4185812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185812 prefixEnd_4185812 := by exact prefixLift 4185812
  have htrace : WordTrace (prefixWord ++ tailWord_4185812) baseStart_4185812 baseEnd_4185812 := by
    simpa [prefixWord, tailWord_4185812, baseEnd_4185812] using wordTrace_append hprefix tailTrace_4185812
  have hstable : (prefixWord ++ tailWord_4185812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185812).length < 2 ^ (prefixWord ++ tailWord_4185812).sum := by decide
  have hdescent : baseEnd_4185812 < baseStart_4185812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185815 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 4]
def baseStart_4185815 : Nat := 118140960795 + 4185815 * 2 ^ 59
def prefixEnd_4185815 : Nat := 4983230072969 + 3 ^ 40 * 4185815 * 2
def baseEnd_4185815 : Nat := 2149335025799645713262293

theorem tailTrace_4185815 : CollatzResearch.WordTrace tailWord_4185815 prefixEnd_4185815 2149335025799645713262293 := by
  unfold tailWord_4185815
  simp only [CollatzResearch.WordTrace]
  refine ⟨152669215330514610132582899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101779476887009740088388599 152669215330514610132582899)
  ·
    refine ⟨229003822995771915198874349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152669215330514610132582899 229003822995771915198874349)
    ·
      refine ⟨85876433623414468199577881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229003822995771915198874349 85876433623414468199577881)
      ·
        refine ⟨64407325217560851149683411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85876433623414468199577881 64407325217560851149683411)
        ·
          refine ⟨96610987826341276724525117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64407325217560851149683411 96610987826341276724525117)
          ·
            refine ⟨36229120434877978771696919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96610987826341276724525117 36229120434877978771696919)
            ·
              refine ⟨54343680652316968157545379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36229120434877978771696919 54343680652316968157545379)
              ·
                refine ⟨81515520978475452236318069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54343680652316968157545379 81515520978475452236318069)
                ·
                  refine ⟨7642080091732073647154819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81515520978475452236318069 7642080091732073647154819)
                  ·
                    refine ⟨11463120137598110470732229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7642080091732073647154819 11463120137598110470732229)
                    ·
                      refine ⟨2149335025799645713262293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11463120137598110470732229 2149335025799645713262293)
                      ·
                        rfl

theorem cell23_4185815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_4185815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185815 prefixEnd_4185815 := by exact prefixLift 4185815
  have htrace : WordTrace (prefixWord ++ tailWord_4185815) baseStart_4185815 baseEnd_4185815 := by
    simpa [prefixWord, tailWord_4185815, baseEnd_4185815] using wordTrace_append hprefix tailTrace_4185815
  have hstable : (prefixWord ++ tailWord_4185815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185815).length < 2 ^ (prefixWord ++ tailWord_4185815).sum := by decide
  have hdescent : baseEnd_4185815 < baseStart_4185815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185832 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_4185832 : Nat := 118140960795 + 4185832 * 2 ^ 59
def prefixEnd_4185832 : Nat := 4983230072969 + 3 ^ 40 * 4185832 * 2
def baseEnd_4185832 : Nat := 2149343754970772146749715

theorem tailTrace_4185832 : CollatzResearch.WordTrace tailWord_4185832 prefixEnd_4185832 2149343754970772146749715 := by
  unfold tailWord_4185832
  simp only [CollatzResearch.WordTrace]
  refine ⟨76334917685726511017975875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101779890247635348023967833 76334917685726511017975875)
  ·
    refine ⟨114502376528589766526963813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76334917685726511017975875 114502376528589766526963813)
    ·
      refine ⟨21469195599110581223805715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114502376528589766526963813 21469195599110581223805715)
      ·
        refine ⟨32203793398665871835708573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21469195599110581223805715 32203793398665871835708573)
        ·
          refine ⟨12076422524499701938390715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32203793398665871835708573 12076422524499701938390715)
          ·
            refine ⟨18114633786749552907586073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12076422524499701938390715 18114633786749552907586073)
            ·
              refine ⟨13585975340062164680689555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18114633786749552907586073 13585975340062164680689555)
              ·
                refine ⟨20378963010093247021034333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13585975340062164680689555 20378963010093247021034333)
                ·
                  refine ⟨7642111128784967632887875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20378963010093247021034333 7642111128784967632887875)
                  ·
                    refine ⟨11463166693177451449331813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7642111128784967632887875 11463166693177451449331813)
                    ·
                      refine ⟨2149343754970772146749715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11463166693177451449331813 2149343754970772146749715)
                      ·
                        rfl

theorem cell23_4185832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_4185832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185832 prefixEnd_4185832 := by exact prefixLift 4185832
  have htrace : WordTrace (prefixWord ++ tailWord_4185832) baseStart_4185832 baseEnd_4185832 := by
    simpa [prefixWord, tailWord_4185832, baseEnd_4185832] using wordTrace_append hprefix tailTrace_4185832
  have hstable : (prefixWord ++ tailWord_4185832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185832).length < 2 ^ (prefixWord ++ tailWord_4185832).sum := by decide
  have hdescent : baseEnd_4185832 < baseStart_4185832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185842 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 4, 4]
def baseStart_4185842 : Nat := 118140960795 + 4185842 * 2 ^ 59
def prefixEnd_4185842 : Nat := 4983230072969 + 3 ^ 40 * 4185842 * 2
def baseEnd_4185842 : Nat := 716449629925772369208223

theorem tailTrace_4185842 : CollatzResearch.WordTrace tailWord_4185842 prefixEnd_4185842 716449629925772369208223 := by
  unfold tailWord_4185842
  simp only [CollatzResearch.WordTrace]
  refine ⟨38167550025354198435953945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101780133400944529162543853 38167550025354198435953945)
  ·
    refine ⟨28625662519015648826965459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38167550025354198435953945 28625662519015648826965459)
    ·
      refine ⟨42938493778523473240448189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28625662519015648826965459 42938493778523473240448189)
      ·
        refine ⟨16101935166946302465168071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42938493778523473240448189 16101935166946302465168071)
        ·
          refine ⟨24152902750419453697752107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16101935166946302465168071 24152902750419453697752107)
          ·
            refine ⟨36229354125629180546628161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24152902750419453697752107 36229354125629180546628161)
            ·
              refine ⟨27172015594221885409971121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36229354125629180546628161 27172015594221885409971121)
              ·
                refine ⟨20379011695666414057478341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27172015594221885409971121 20379011695666414057478341)
                ·
                  refine ⟨3821064692937452635777189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20379011695666414057478341 3821064692937452635777189)
                  ·
                    refine ⟨716449629925772369208223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3821064692937452635777189 716449629925772369208223)
                    ·
                      rfl

theorem cell23_4185842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_4185842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185842 prefixEnd_4185842 := by exact prefixLift 4185842
  have htrace : WordTrace (prefixWord ++ tailWord_4185842) baseStart_4185842 baseEnd_4185842 := by
    simpa [prefixWord, tailWord_4185842, baseEnd_4185842] using wordTrace_append hprefix tailTrace_4185842
  have hstable : (prefixWord ++ tailWord_4185842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185842).length < 2 ^ (prefixWord ++ tailWord_4185842).sum := by decide
  have hdescent : baseEnd_4185842 < baseStart_4185842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185846 : List Nat := [5, 1, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_4185846 : Nat := 118140960795 + 4185846 * 2 ^ 59
def prefixEnd_4185846 : Nat := 4983230072969 + 3 ^ 40 * 4185846 * 2
def baseEnd_4185846 : Nat := 716450314566645030658217

theorem tailTrace_4185846 : CollatzResearch.WordTrace tailWord_4185846 prefixEnd_4185846 716450314566645030658217 := by
  unfold tailWord_4185846
  simp only [CollatzResearch.WordTrace]
  refine ⟨9541896624587643901685087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101780230662268201617974261 9541896624587643901685087)
  ·
    refine ⟨14312844936881465852527631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9541896624587643901685087 14312844936881465852527631)
    ·
      refine ⟨21469267405322198778791447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14312844936881465852527631 21469267405322198778791447)
      ·
        refine ⟨32203901107983298168187171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21469267405322198778791447 32203901107983298168187171)
        ·
          refine ⟨48305851661974947252280757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32203901107983298168187171 48305851661974947252280757)
          ·
            refine ⟨4528673593310151304901321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48305851661974947252280757 4528673593310151304901321)
            ·
              refine ⟨3396505194982613478675991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4528673593310151304901321 3396505194982613478675991)
              ·
                refine ⟨5094757792473920218013987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3396505194982613478675991 5094757792473920218013987)
                ·
                  refine ⟨7642136688710880327020981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5094757792473920218013987 7642136688710880327020981)
                  ·
                    refine ⟨716450314566645030658217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7642136688710880327020981 716450314566645030658217)
                    ·
                      rfl

theorem cell23_4185846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_4185846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185846 prefixEnd_4185846 := by exact prefixLift 4185846
  have htrace : WordTrace (prefixWord ++ tailWord_4185846) baseStart_4185846 baseEnd_4185846 := by
    simpa [prefixWord, tailWord_4185846, baseEnd_4185846] using wordTrace_append hprefix tailTrace_4185846
  have hstable : (prefixWord ++ tailWord_4185846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185846).length < 2 ^ (prefixWord ++ tailWord_4185846).sum := by decide
  have hdescent : baseEnd_4185846 < baseStart_4185846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185866 : List Nat := [3, 1, 2, 2, 1, 4, 2, 1, 3, 2, 2]
def baseStart_4185866 : Nat := 118140960795 + 4185866 * 2 ^ 59
def prefixEnd_4185866 : Nat := 4983230072969 + 3 ^ 40 * 4185866 * 2
def baseEnd_4185866 : Nat := 2149361213313025013724559

theorem tailTrace_4185866 : CollatzResearch.WordTrace tailWord_4185866 prefixEnd_4185866 2149361213313025013724559 := by
  unfold tailWord_4185866
  simp only [CollatzResearch.WordTrace]
  refine ⟨38167768863332461460672363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101780716968886563895126301 38167768863332461460672363)
  ·
    refine ⟨57251653294998692191008545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38167768863332461460672363 57251653294998692191008545)
    ·
      refine ⟨42938739971249019143256409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57251653294998692191008545 42938739971249019143256409)
      ·
        refine ⟨32204054978436764357442307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42938739971249019143256409 32204054978436764357442307)
        ·
          refine ⟨48306082467655146536163461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32204054978436764357442307 48306082467655146536163461)
          ·
            refine ⟨9057390462685339975530649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48306082467655146536163461 9057390462685339975530649)
            ·
              refine ⟨6793042847014004981647987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9057390462685339975530649 6793042847014004981647987)
              ·
                refine ⟨10189564270521007472471981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6793042847014004981647987 10189564270521007472471981)
                ·
                  refine ⟨3821086601445377802176993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10189564270521007472471981 3821086601445377802176993)
                  ·
                    refine ⟨2865814951084033351632745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3821086601445377802176993 2865814951084033351632745)
                    ·
                      refine ⟨2149361213313025013724559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2865814951084033351632745 2149361213313025013724559)
                      ·
                        rfl

theorem cell23_4185866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_4185866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185866 prefixEnd_4185866 := by exact prefixLift 4185866
  have htrace : WordTrace (prefixWord ++ tailWord_4185866) baseStart_4185866 baseEnd_4185866 := by
    simpa [prefixWord, tailWord_4185866, baseEnd_4185866] using wordTrace_append hprefix tailTrace_4185866
  have hstable : (prefixWord ++ tailWord_4185866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185866).length < 2 ^ (prefixWord ++ tailWord_4185866).sum := by decide
  have hdescent : baseEnd_4185866 < baseStart_4185866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185879 : List Nat := [1, 1, 3, 4, 2, 3, 1, 1, 1, 2, 4]
def baseStart_4185879 : Nat := 118140960795 + 4185879 * 2 ^ 59
def prefixEnd_4185879 : Nat := 4983230072969 + 3 ^ 40 * 4185879 * 2
def baseEnd_4185879 : Nat := 2149367888561533462861999

theorem tailTrace_4185879 : CollatzResearch.WordTrace tailWord_4185879 prefixEnd_4185879 2149367888561533462861999 := by
  unfold tailWord_4185879
  simp only [CollatzResearch.WordTrace]
  refine ⟨152671549602282749062912691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101781033068188499375275127 152671549602282749062912691)
  ·
    refine ⟨229007324403424123594369037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152671549602282749062912691 229007324403424123594369037)
    ·
      refine ⟨85877746651284046347888389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229007324403424123594369037 85877746651284046347888389)
      ·
        refine ⟨16102077497115758690229073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85877746651284046347888389 16102077497115758690229073)
        ·
          refine ⟨12076558122836819017671805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16102077497115758690229073 12076558122836819017671805)
          ·
            refine ⟨4528709296063807131626927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12076558122836819017671805 4528709296063807131626927)
            ·
              refine ⟨6793063944095710697440391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528709296063807131626927 6793063944095710697440391)
              ·
                refine ⟨10189595916143566046160587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6793063944095710697440391 10189595916143566046160587)
                ·
                  refine ⟨15284393874215349069240881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10189595916143566046160587 15284393874215349069240881)
                  ·
                    refine ⟨11463295405661511801930661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15284393874215349069240881 11463295405661511801930661)
                    ·
                      refine ⟨2149367888561533462861999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11463295405661511801930661 2149367888561533462861999)
                      ·
                        rfl

theorem cell23_4185879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_4185879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185879 prefixEnd_4185879 := by exact prefixLift 4185879
  have htrace : WordTrace (prefixWord ++ tailWord_4185879) baseStart_4185879 baseEnd_4185879 := by
    simpa [prefixWord, tailWord_4185879, baseEnd_4185879] using wordTrace_append hprefix tailTrace_4185879
  have hstable : (prefixWord ++ tailWord_4185879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185879).length < 2 ^ (prefixWord ++ tailWord_4185879).sum := by decide
  have hdescent : baseEnd_4185879 < baseStart_4185879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185925 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 1, 3, 5]
def baseStart_4185925 : Nat := 118140960795 + 4185925 * 2 ^ 59
def prefixEnd_4185925 : Nat := 4983230072969 + 3 ^ 40 * 4185925 * 2
def baseEnd_4185925 : Nat := 2149391508671640282886787

theorem tailTrace_4185925 : CollatzResearch.WordTrace tailWord_4185925 prefixEnd_4185925 2149391508671640282886787 := by
  unfold tailWord_4185925
  simp only [CollatzResearch.WordTrace]
  refine ⟨152673227360116098919087229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101782151573410732612724819 152673227360116098919087229)
  ·
    refine ⟨57252460260043537094657711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152673227360116098919087229 57252460260043537094657711)
    ·
      refine ⟨85878690390065305641986567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57252460260043537094657711 85878690390065305641986567)
      ·
        refine ⟨128818035585097958462979851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85878690390065305641986567 128818035585097958462979851)
        ·
          refine ⟨193227053377646937694469777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128818035585097958462979851 193227053377646937694469777)
          ·
            refine ⟨144920290033235203270852333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193227053377646937694469777 144920290033235203270852333)
            ·
              refine ⟨54345108762463201226569625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144920290033235203270852333 54345108762463201226569625)
              ·
                refine ⟨40758831571847400919927219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54345108762463201226569625 40758831571847400919927219)
                ·
                  refine ⟨61138247357771101379890829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40758831571847400919927219 61138247357771101379890829)
                  ·
                    refine ⟨22926842759164163017459061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61138247357771101379890829 22926842759164163017459061)
                    ·
                      refine ⟨2149391508671640282886787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22926842759164163017459061 2149391508671640282886787)
                      ·
                        rfl

theorem cell23_4185925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_4185925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185925 prefixEnd_4185925 := by exact prefixLift 4185925
  have htrace : WordTrace (prefixWord ++ tailWord_4185925) baseStart_4185925 baseEnd_4185925 := by
    simpa [prefixWord, tailWord_4185925, baseEnd_4185925] using wordTrace_append hprefix tailTrace_4185925
  have hstable : (prefixWord ++ tailWord_4185925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185925).length < 2 ^ (prefixWord ++ tailWord_4185925).sum := by decide
  have hdescent : baseEnd_4185925 < baseStart_4185925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185933 : List Nat := [1, 6, 1, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_4185933 : Nat := 118140960795 + 4185933 * 2 ^ 59
def prefixEnd_4185933 : Nat := 4983230072969 + 3 ^ 40 * 4185933 * 2
def baseEnd_4185933 : Nat := 2149395616516876251586751

theorem tailTrace_4185933 : CollatzResearch.WordTrace tailWord_4185933 prefixEnd_4185933 2149395616516876251586751 := by
  unfold tailWord_4185933
  simp only [CollatzResearch.WordTrace]
  refine ⟨152673519144087116285378453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101782346096058077523585635 152673519144087116285378453)
  ·
    refine ⟨7156571209879083575877115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152673519144087116285378453 7156571209879083575877115)
    ·
      refine ⟨10734856814818625363815673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7156571209879083575877115 10734856814818625363815673)
      ·
        refine ⟨8051142611113969022861755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10734856814818625363815673 8051142611113969022861755)
        ·
          refine ⟨12076713916670953534292633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8051142611113969022861755 12076713916670953534292633)
          ·
            refine ⟨9057535437503215150719475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12076713916670953534292633 9057535437503215150719475)
            ·
              refine ⟨13586303156254822726079213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9057535437503215150719475 13586303156254822726079213)
              ·
                refine ⟨5094863683595558522279705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13586303156254822726079213 5094863683595558522279705)
                ·
                  refine ⟨3821147762696668891709779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5094863683595558522279705 3821147762696668891709779)
                  ·
                    refine ⟨5731721644045003337564669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3821147762696668891709779 5731721644045003337564669)
                    ·
                      refine ⟨2149395616516876251586751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5731721644045003337564669 2149395616516876251586751)
                      ·
                        rfl

theorem cell23_4185933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_4185933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185933 prefixEnd_4185933 := by exact prefixLift 4185933
  have htrace : WordTrace (prefixWord ++ tailWord_4185933) baseStart_4185933 baseEnd_4185933 := by
    simpa [prefixWord, tailWord_4185933, baseEnd_4185933] using wordTrace_append hprefix tailTrace_4185933
  have hstable : (prefixWord ++ tailWord_4185933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185933).length < 2 ^ (prefixWord ++ tailWord_4185933).sum := by decide
  have hdescent : baseEnd_4185933 < baseStart_4185933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185943 : List Nat := [1, 1, 3, 2, 5, 2, 1, 2, 1, 3, 2]
def baseStart_4185943 : Nat := 118140960795 + 4185943 * 2 ^ 59
def prefixEnd_4185943 : Nat := 4983230072969 + 3 ^ 40 * 4185943 * 2
def baseEnd_4185943 : Nat := 2149400751323421212461705

theorem tailTrace_4185943 : CollatzResearch.WordTrace tailWord_4185943 prefixEnd_4185943 2149400751323421212461705 := by
  unfold tailWord_4185943
  simp only [CollatzResearch.WordTrace]
  refine ⟨152673883874050887993242483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101782589249367258662161655 152673883874050887993242483)
  ·
    refine ⟨229010825811076331989863725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152673883874050887993242483 229010825811076331989863725)
    ·
      refine ⟨85879059679153624496198897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229010825811076331989863725 85879059679153624496198897)
      ·
        refine ⟨64409294759365218372149173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85879059679153624496198897 64409294759365218372149173)
        ·
          refine ⟨6038371383690489222388985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64409294759365218372149173 6038371383690489222388985)
          ·
            refine ⟨4528778537767866916791739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6038371383690489222388985 4528778537767866916791739)
            ·
              refine ⟨6793167806651800375187609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528778537767866916791739 6793167806651800375187609)
              ·
                refine ⟨5094875854988850281390707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6793167806651800375187609 5094875854988850281390707)
                ·
                  refine ⟨7642313782483275422086061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5094875854988850281390707 7642313782483275422086061)
                  ·
                    refine ⟨2865867668431228283282273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7642313782483275422086061 2865867668431228283282273)
                    ·
                      refine ⟨2149400751323421212461705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2865867668431228283282273 2149400751323421212461705)
                      ·
                        rfl

theorem cell23_4185943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_4185943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185943 prefixEnd_4185943 := by exact prefixLift 4185943
  have htrace : WordTrace (prefixWord ++ tailWord_4185943) baseStart_4185943 baseEnd_4185943 := by
    simpa [prefixWord, tailWord_4185943, baseEnd_4185943] using wordTrace_append hprefix tailTrace_4185943
  have hstable : (prefixWord ++ tailWord_4185943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185943).length < 2 ^ (prefixWord ++ tailWord_4185943).sum := by decide
  have hdescent : baseEnd_4185943 < baseStart_4185943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185945 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 9]
def baseStart_4185945 : Nat := 118140960795 + 4185945 * 2 ^ 59
def prefixEnd_4185945 : Nat := 4983230072969 + 3 ^ 40 * 4185945 * 2
def baseEnd_4185945 : Nat := 238822419809414467181855

theorem tailTrace_4185945 : CollatzResearch.WordTrace tailWord_4185945 prefixEnd_4185945 238822419809414467181855 := by
  unfold tailWord_4185945
  simp only [CollatzResearch.WordTrace]
  refine ⟨152673956820043642334815289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101782637880029094889876859 152673956820043642334815289)
  ·
    refine ⟨114505467615032731751111467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152673956820043642334815289 114505467615032731751111467)
    ·
      refine ⟨171758201422549097626667201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114505467615032731751111467 171758201422549097626667201)
      ·
        refine ⟨128818651066911823220000401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171758201422549097626667201 128818651066911823220000401)
        ·
          refine ⟨96613988300183867415000301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128818651066911823220000401 96613988300183867415000301)
          ·
            refine ⟨36230245612568950280625113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96613988300183867415000301 36230245612568950280625113)
            ·
              refine ⟨27172684209426712710468835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36230245612568950280625113 27172684209426712710468835)
              ·
                refine ⟨40759026314140069065703253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27172684209426712710468835 40759026314140069065703253)
                ·
                  refine ⟨238822419809414467181855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40759026314140069065703253 238822419809414467181855)
                  ·
                    rfl

theorem cell23_4185945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 9].length) (baseStart_4185945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185945 prefixEnd_4185945 := by exact prefixLift 4185945
  have htrace : WordTrace (prefixWord ++ tailWord_4185945) baseStart_4185945 baseEnd_4185945 := by
    simpa [prefixWord, tailWord_4185945, baseEnd_4185945] using wordTrace_append hprefix tailTrace_4185945
  have hstable : (prefixWord ++ tailWord_4185945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185945).length < 2 ^ (prefixWord ++ tailWord_4185945).sum := by decide
  have hdescent : baseEnd_4185945 < baseStart_4185945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185956 : List Nat := [2, 3, 1, 1, 5, 1, 1, 2, 1, 4, 2]
def baseStart_4185956 : Nat := 118140960795 + 4185956 * 2 ^ 59
def prefixEnd_4185956 : Nat := 4983230072969 + 3 ^ 40 * 4185956 * 2
def baseEnd_4185956 : Nat := 2149407426571929661599145

theorem tailTrace_4185956 : CollatzResearch.WordTrace tailWord_4185956 prefixEnd_4185956 2149407426571929661599145 := by
  unfold tailWord_4185956
  simp only [CollatzResearch.WordTrace]
  refine ⟨76337179011501895606732861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101782905348669194142310481 76337179011501895606732861)
  ·
    refine ⟨28626442129313210852524823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76337179011501895606732861 28626442129313210852524823)
    ·
      refine ⟨42939663193969816278787235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28626442129313210852524823 42939663193969816278787235)
      ·
        refine ⟨64409494790954724418180853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42939663193969816278787235 64409494790954724418180853)
        ·
          refine ⟨6038390136652005414204455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64409494790954724418180853 6038390136652005414204455)
          ·
            refine ⟨9057585204978008121306683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6038390136652005414204455 9057585204978008121306683)
            ·
              refine ⟨13586377807467012181960025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9057585204978008121306683 13586377807467012181960025)
              ·
                refine ⟨10189783355600259136470019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13586377807467012181960025 10189783355600259136470019)
                ·
                  refine ⟨15284675033400388704705029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10189783355600259136470019 15284675033400388704705029)
                  ·
                    refine ⟨2865876568762572882132193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15284675033400388704705029 2865876568762572882132193)
                    ·
                      refine ⟨2149407426571929661599145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2865876568762572882132193 2149407426571929661599145)
                      ·
                        rfl

theorem cell23_4185956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_4185956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185956 prefixEnd_4185956 := by exact prefixLift 4185956
  have htrace : WordTrace (prefixWord ++ tailWord_4185956) baseStart_4185956 baseEnd_4185956 := by
    simpa [prefixWord, tailWord_4185956, baseEnd_4185956] using wordTrace_append hprefix tailTrace_4185956
  have hstable : (prefixWord ++ tailWord_4185956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185956).length < 2 ^ (prefixWord ++ tailWord_4185956).sum := by decide
  have hdescent : baseEnd_4185956 < baseStart_4185956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185973 : List Nat := [1, 3, 4, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_4185973 : Nat := 118140960795 + 4185973 * 2 ^ 59
def prefixEnd_4185973 : Nat := 4983230072969 + 3 ^ 40 * 4185973 * 2
def baseEnd_4185973 : Nat := 2149416155743056095086567

theorem tailTrace_4185973 : CollatzResearch.WordTrace tailWord_4185973 prefixEnd_4185973 2149416155743056095086567 := by
  unfold tailWord_4185973
  simp only [CollatzResearch.WordTrace]
  refine ⟨152674978063942203116834573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101783318709294802077889715 152674978063942203116834573)
  ·
    refine ⟨57253116773978326168812965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152674978063942203116834573 57253116773978326168812965)
    ·
      refine ⟨10734959395120936156652431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57253116773978326168812965 10734959395120936156652431)
      ·
        refine ⟨16102439092681404234978647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10734959395120936156652431 16102439092681404234978647)
        ·
          refine ⟨24153658639022106352467971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16102439092681404234978647 24153658639022106352467971)
          ·
            refine ⟨36230487958533159528701957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24153658639022106352467971 36230487958533159528701957)
            ·
              refine ⟨6793216492224967411631617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36230487958533159528701957 6793216492224967411631617)
              ·
                refine ⟨5094912369168725558723713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6793216492224967411631617 5094912369168725558723713)
                ·
                  refine ⟨3821184276876544169042785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5094912369168725558723713 3821184276876544169042785)
                  ·
                    refine ⟨2865888207657408126782089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3821184276876544169042785 2865888207657408126782089)
                    ·
                      refine ⟨2149416155743056095086567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2865888207657408126782089 2149416155743056095086567)
                      ·
                        rfl

theorem cell23_4185973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_4185973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185973 prefixEnd_4185973 := by exact prefixLift 4185973
  have htrace : WordTrace (prefixWord ++ tailWord_4185973) baseStart_4185973 baseEnd_4185973 := by
    simpa [prefixWord, tailWord_4185973, baseEnd_4185973] using wordTrace_append hprefix tailTrace_4185973
  have hstable : (prefixWord ++ tailWord_4185973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185973).length < 2 ^ (prefixWord ++ tailWord_4185973).sum := by decide
  have hdescent : baseEnd_4185973 < baseStart_4185973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185975 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 5, 7]
def baseStart_4185975 : Nat := 118140960795 + 4185975 * 2 ^ 59
def prefixEnd_4185975 : Nat := 4983230072969 + 3 ^ 40 * 4185975 * 2
def baseEnd_4185975 : Nat := 716472394234788362420519

theorem tailTrace_4185975 : CollatzResearch.WordTrace tailWord_4185975 prefixEnd_4185975 716472394234788362420519 := by
  unfold tailWord_4185975
  simp only [CollatzResearch.WordTrace]
  refine ⟨152675051009934957458407379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101783367339956638305604919 152675051009934957458407379)
  ·
    refine ⟨229012576514902436187611069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152675051009934957458407379 229012576514902436187611069)
    ·
      refine ⟨85879716193088413570354151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229012576514902436187611069 85879716193088413570354151)
      ·
        refine ⟨128819574289632620355531227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85879716193088413570354151 128819574289632620355531227)
        ·
          refine ⟨193229361434448930533296841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128819574289632620355531227 193229361434448930533296841)
          ·
            refine ⟨144922021075836697899972631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193229361434448930533296841 144922021075836697899972631)
            ·
              refine ⟨217383031613755046849958947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144922021075836697899972631 217383031613755046849958947)
              ·
                refine ⟨326074547420632570274938421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217383031613755046849958947 326074547420632570274938421)
                ·
                  refine ⟨30569488820684303463275477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 326074547420632570274938421 30569488820684303463275477)
                  ·
                    refine ⟨716472394234788362420519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30569488820684303463275477 716472394234788362420519)
                    ·
                      rfl

theorem cell23_4185975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_4185975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4185975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4185975 prefixEnd_4185975 := by exact prefixLift 4185975
  have htrace : WordTrace (prefixWord ++ tailWord_4185975) baseStart_4185975 baseEnd_4185975 := by
    simpa [prefixWord, tailWord_4185975, baseEnd_4185975] using wordTrace_append hprefix tailTrace_4185975
  have hstable : (prefixWord ++ tailWord_4185975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185975).length < 2 ^ (prefixWord ++ tailWord_4185975).sum := by decide
  have hdescent : baseEnd_4185975 < baseStart_4185975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186024 : List Nat := [2, 1, 6, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_4186024 : Nat := 118140960795 + 4186024 * 2 ^ 59
def prefixEnd_4186024 : Nat := 4983230072969 + 3 ^ 40 * 4186024 * 2
def baseEnd_4186024 : Nat := 2149442343256435395548833

theorem tailTrace_4186024 : CollatzResearch.WordTrace tailWord_4186024 prefixEnd_4186024 2149442343256435395548833 := by
  unfold tailWord_4186024
  simp only [CollatzResearch.WordTrace]
  refine ⟨76338419093378719413470563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101784558791171625884627417 76338419093378719413470563)
  ·
    refine ⟨114507628640068079120205845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76338419093378719413470563 114507628640068079120205845)
    ·
      refine ⟨5367545092503191208759649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 114507628640068079120205845 5367545092503191208759649)
      ·
        refine ⟨4025658819377393406569737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5367545092503191208759649 4025658819377393406569737)
        ·
          refine ⟨3019244114533045054927303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4025658819377393406569737 3019244114533045054927303)
          ·
            refine ⟨4528866171799567582390955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3019244114533045054927303 4528866171799567582390955)
            ·
              refine ⟨6793299257699351373586433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528866171799567582390955 6793299257699351373586433)
              ·
                refine ⟨5094974443274513530189825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6793299257699351373586433 5094974443274513530189825)
                ·
                  refine ⟨3821230832455885147642369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5094974443274513530189825 3821230832455885147642369)
                  ·
                    refine ⟨2865923124341913860731777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3821230832455885147642369 2865923124341913860731777)
                    ·
                      refine ⟨2149442343256435395548833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2865923124341913860731777 2149442343256435395548833)
                      ·
                        rfl

theorem cell23_4186024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_4186024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186024 prefixEnd_4186024 := by exact prefixLift 4186024
  have htrace : WordTrace (prefixWord ++ tailWord_4186024) baseStart_4186024 baseEnd_4186024 := by
    simpa [prefixWord, tailWord_4186024, baseEnd_4186024] using wordTrace_append hprefix tailTrace_4186024
  have hstable : (prefixWord ++ tailWord_4186024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186024).length < 2 ^ (prefixWord ++ tailWord_4186024).sum := by decide
  have hdescent : baseEnd_4186024 < baseStart_4186024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186046 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2]
def baseStart_4186046 : Nat := 118140960795 + 4186046 * 2 ^ 59
def prefixEnd_4186046 : Nat := 4983230072969 + 3 ^ 40 * 4186046 * 2
def baseEnd_4186046 : Nat := 2149453639830834309473731

theorem tailTrace_4186046 : CollatzResearch.WordTrace tailWord_4186046 prefixEnd_4186046 2149453639830834309473731 := by
  unfold tailWord_4186046
  simp only [CollatzResearch.WordTrace]
  refine ⟨19084705074084717073030249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101785093728451824389494661 19084705074084717073030249)
  ·
    refine ⟨14313528805563537804772687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19084705074084717073030249 14313528805563537804772687)
    ·
      refine ⟨21470293208345306707159031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14313528805563537804772687 21470293208345306707159031)
      ·
        refine ⟨32205439812517960060738547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21470293208345306707159031 32205439812517960060738547)
        ·
          refine ⟨48308159718776940091107821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32205439812517960060738547 48308159718776940091107821)
          ·
            refine ⟨18115559894541352534165433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48308159718776940091107821 18115559894541352534165433)
            ·
              refine ⟨13586669920906014400624075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18115559894541352534165433 13586669920906014400624075)
              ·
                refine ⟨20380004881359021600936113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13586669920906014400624075 20380004881359021600936113)
                ·
                  refine ⟨15285003661019266200702085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20380004881359021600936113 15285003661019266200702085)
                  ·
                    refine ⟨2865938186441112412631641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15285003661019266200702085 2865938186441112412631641)
                    ·
                      refine ⟨2149453639830834309473731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2865938186441112412631641 2149453639830834309473731)
                      ·
                        rfl

theorem cell23_4186046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_4186046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186046 prefixEnd_4186046 := by exact prefixLift 4186046
  have htrace : WordTrace (prefixWord ++ tailWord_4186046) baseStart_4186046 baseEnd_4186046 := by
    simpa [prefixWord, tailWord_4186046, baseEnd_4186046] using wordTrace_append hprefix tailTrace_4186046
  have hstable : (prefixWord ++ tailWord_4186046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186046).length < 2 ^ (prefixWord ++ tailWord_4186046).sum := by decide
  have hdescent : baseEnd_4186046 < baseStart_4186046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186096 : List Nat := [2, 1, 1, 1, 3, 2, 5, 1, 3, 1, 3]
def baseStart_4186096 : Nat := 118140960795 + 4186096 * 2 ^ 59
def prefixEnd_4186096 : Nat := 4983230072969 + 3 ^ 40 * 4186096 * 2
def baseEnd_4186096 : Nat := 2149479313863559113848501

theorem tailTrace_4186096 : CollatzResearch.WordTrace tailWord_4186096 prefixEnd_4186096 2149479313863559113848501 := by
  unfold tailWord_4186096
  simp only [CollatzResearch.WordTrace]
  refine ⟨76339732121248297561781071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101786309494997730082374761 76339732121248297561781071)
  ·
    refine ⟨114509598181872446342671607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76339732121248297561781071 114509598181872446342671607)
    ·
      refine ⟨171764397272808669514007411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114509598181872446342671607 171764397272808669514007411)
      ·
        refine ⟨257646595909213004271011117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171764397272808669514007411 257646595909213004271011117)
        ·
          refine ⟨96617473465954876601629169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257646595909213004271011117 96617473465954876601629169)
          ·
            refine ⟨72463105099466157451221877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96617473465954876601629169 72463105099466157451221877)
            ·
              refine ⟨6793416103074952261052051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72463105099466157451221877 6793416103074952261052051)
              ·
                refine ⟨10190124154612428391578077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6793416103074952261052051 10190124154612428391578077)
                ·
                  refine ⟨3821296557979660646841779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10190124154612428391578077 3821296557979660646841779)
                  ·
                    refine ⟨5731944836969490970262669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3821296557979660646841779 5731944836969490970262669)
                    ·
                      refine ⟨2149479313863559113848501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5731944836969490970262669 2149479313863559113848501)
                      ·
                        rfl

theorem cell23_4186096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 3, 1, 3].length) (baseStart_4186096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186096 prefixEnd_4186096 := by exact prefixLift 4186096
  have htrace : WordTrace (prefixWord ++ tailWord_4186096) baseStart_4186096 baseEnd_4186096 := by
    simpa [prefixWord, tailWord_4186096, baseEnd_4186096] using wordTrace_append hprefix tailTrace_4186096
  have hstable : (prefixWord ++ tailWord_4186096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186096).length < 2 ^ (prefixWord ++ tailWord_4186096).sum := by decide
  have hdescent : baseEnd_4186096 < baseStart_4186096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186133 : List Nat := [1, 3, 2, 1, 5, 1, 3, 1, 1, 5]
def baseStart_4186133 : Nat := 118140960795 + 4186133 * 2 ^ 59
def prefixEnd_4186133 : Nat := 4983230072969 + 3 ^ 40 * 4186133 * 2
def baseEnd_4186133 : Nat := 716499437549258489695277

theorem tailTrace_4186133 : CollatzResearch.WordTrace tailWord_4186133 prefixEnd_4186133 716499437549258489695277 := by
  unfold tailWord_4186133
  simp only [CollatzResearch.WordTrace]
  refine ⟨152680813743362550442659053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101787209162241700295106035 152680813743362550442659053)
  ·
    refine ⟨57255305153760956415997145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152680813743362550442659053 57255305153760956415997145)
    ·
      refine ⟨42941478865320717311997859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57255305153760956415997145 42941478865320717311997859)
      ·
        refine ⟨64412218297981075967996789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42941478865320717311997859 64412218297981075967996789)
        ·
          refine ⟨6038645465435725871999699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64412218297981075967996789 6038645465435725871999699)
          ·
            refine ⟨9057968198153588807999549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6038645465435725871999699 9057968198153588807999549)
            ·
              refine ⟨3396738074307595802999831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9057968198153588807999549 3396738074307595802999831)
              ·
                refine ⟨5095107111461393704499747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3396738074307595802999831 5095107111461393704499747)
                ·
                  refine ⟨7642660667192090556749621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095107111461393704499747 7642660667192090556749621)
                  ·
                    refine ⟨716499437549258489695277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7642660667192090556749621 716499437549258489695277)
                    ·
                      rfl

theorem cell23_4186133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_4186133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186133 prefixEnd_4186133 := by exact prefixLift 4186133
  have htrace : WordTrace (prefixWord ++ tailWord_4186133) baseStart_4186133 baseEnd_4186133 := by
    simpa [prefixWord, tailWord_4186133, baseEnd_4186133] using wordTrace_append hprefix tailTrace_4186133
  have hstable : (prefixWord ++ tailWord_4186133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186133).length < 2 ^ (prefixWord ++ tailWord_4186133).sum := by decide
  have hdescent : baseEnd_4186133 < baseStart_4186133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186186 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 4, 1, 3]
def baseStart_4186186 : Nat := 118140960795 + 4186186 * 2 ^ 59
def prefixEnd_4186186 : Nat := 4983230072969 + 3 ^ 40 * 4186186 * 2
def baseEnd_4186186 : Nat := 2149525527122463761723087

theorem tailTrace_4186186 : CollatzResearch.WordTrace tailWord_4186186 prefixEnd_4186186 2149525527122463761723087 := by
  unfold tailWord_4186186
  simp only [CollatzResearch.WordTrace]
  refine ⟨38170686703042635123584603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101788497874780360329558941 38170686703042635123584603)
  ·
    refine ⟨57256030054563952685376905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38170686703042635123584603 57256030054563952685376905)
    ·
      refine ⟨42942022540922964514032679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57256030054563952685376905 42942022540922964514032679)
      ·
        refine ⟨64413033811384446771049019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42942022540922964514032679 64413033811384446771049019)
        ·
          refine ⟨96619550717076670156573529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64413033811384446771049019 96619550717076670156573529)
          ·
            refine ⟨72464663037807502617430147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96619550717076670156573529 72464663037807502617430147)
            ·
              refine ⟨108696994556711253926145221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72464663037807502617430147 108696994556711253926145221)
              ·
                refine ⟨20380686479383360111152229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108696994556711253926145221 20380686479383360111152229)
                ·
                  refine ⟨3821378714884380020841043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20380686479383360111152229 3821378714884380020841043)
                  ·
                    refine ⟨5732068072326570031261565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3821378714884380020841043 5732068072326570031261565)
                    ·
                      refine ⟨2149525527122463761723087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5732068072326570031261565 2149525527122463761723087)
                      ·
                        rfl

theorem cell23_4186186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_4186186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186186 prefixEnd_4186186 := by exact prefixLift 4186186
  have htrace : WordTrace (prefixWord ++ tailWord_4186186) baseStart_4186186 baseEnd_4186186 := by
    simpa [prefixWord, tailWord_4186186, baseEnd_4186186] using wordTrace_append hprefix tailTrace_4186186
  have hstable : (prefixWord ++ tailWord_4186186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186186).length < 2 ^ (prefixWord ++ tailWord_4186186).sum := by decide
  have hdescent : baseEnd_4186186 < baseStart_4186186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186190 : List Nat := [4, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3]
def baseStart_4186190 : Nat := 118140960795 + 4186190 * 2 ^ 59
def prefixEnd_4186190 : Nat := 4983230072969 + 3 ^ 40 * 4186190 * 2
def baseEnd_4186190 : Nat := 2149527581045081746073069

theorem tailTrace_4186190 : CollatzResearch.WordTrace tailWord_4186190 prefixEnd_4186190 2149527581045081746073069 := by
  unfold tailWord_4186190
  simp only [CollatzResearch.WordTrace]
  refine ⟨19085361588019506147185503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101788595136104032784989349 19085361588019506147185503)
  ·
    refine ⟨28628042382029259220778255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19085361588019506147185503 28628042382029259220778255)
    ·
      refine ⟨42942063573043888831167383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28628042382029259220778255 42942063573043888831167383)
      ·
        refine ⟨64413095359565833246751075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42942063573043888831167383 64413095359565833246751075)
        ·
          refine ⟨96619643039348749870126613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64413095359565833246751075 96619643039348749870126613)
          ·
            refine ⟨4529045767469472650162185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96619643039348749870126613 4529045767469472650162185)
            ·
              refine ⟨3396784325602104487621639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4529045767469472650162185 3396784325602104487621639)
              ·
                refine ⟨5095176488403156731432459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3396784325602104487621639 5095176488403156731432459)
                ·
                  refine ⟨7642764732604735097148689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095176488403156731432459 7642764732604735097148689)
                  ·
                    refine ⟨5732073549453551322861517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7642764732604735097148689 5732073549453551322861517)
                    ·
                      refine ⟨2149527581045081746073069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5732073549453551322861517 2149527581045081746073069)
                      ·
                        rfl

theorem cell23_4186190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_4186190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186190 prefixEnd_4186190 := by exact prefixLift 4186190
  have htrace : WordTrace (prefixWord ++ tailWord_4186190) baseStart_4186190 baseEnd_4186190 := by
    simpa [prefixWord, tailWord_4186190, baseEnd_4186190] using wordTrace_append hprefix tailTrace_4186190
  have hstable : (prefixWord ++ tailWord_4186190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186190).length < 2 ^ (prefixWord ++ tailWord_4186190).sum := by decide
  have hdescent : baseEnd_4186190 < baseStart_4186190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186220 : List Nat := [2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 3]
def baseStart_4186220 : Nat := 118140960795 + 4186220 * 2 ^ 59
def prefixEnd_4186220 : Nat := 4983230072969 + 3 ^ 40 * 4186220 * 2
def baseEnd_4186220 : Nat := 2149542985464716628697931

theorem tailTrace_4186220 : CollatzResearch.WordTrace tailWord_4186220 prefixEnd_4186220 2149542985464716628697931 := by
  unfold tailWord_4186220
  simp only [CollatzResearch.WordTrace]
  refine ⟨76341993447023682150538057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101789324596031576200717409 76341993447023682150538057)
  ·
    refine ⟨57256495085267761612903543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76341993447023682150538057 57256495085267761612903543)
    ·
      refine ⟨85884742627901642419355315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57256495085267761612903543 85884742627901642419355315)
      ·
        refine ⟨128827113941852463629032973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85884742627901642419355315 128827113941852463629032973)
        ·
          refine ⟨48310167728194673860887365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128827113941852463629032973 48310167728194673860887365)
          ·
            refine ⟨9058156449036501348916381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48310167728194673860887365 9058156449036501348916381)
            ·
              refine ⟨3396808668388688005843643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9058156449036501348916381 3396808668388688005843643)
              ·
                refine ⟨5095213002583032008765465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3396808668388688005843643 5095213002583032008765465)
                ·
                  refine ⟨3821409751937274006574099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5095213002583032008765465 3821409751937274006574099)
                  ·
                    refine ⟨5732114627905911009861149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3821409751937274006574099 5732114627905911009861149)
                    ·
                      refine ⟨2149542985464716628697931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5732114627905911009861149 2149542985464716628697931)
                      ·
                        rfl

theorem cell23_4186220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 3].length) (baseStart_4186220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186220 prefixEnd_4186220 := by exact prefixLift 4186220
  have htrace : WordTrace (prefixWord ++ tailWord_4186220) baseStart_4186220 baseEnd_4186220 := by
    simpa [prefixWord, tailWord_4186220, baseEnd_4186220] using wordTrace_append hprefix tailTrace_4186220
  have hstable : (prefixWord ++ tailWord_4186220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186220).length < 2 ^ (prefixWord ++ tailWord_4186220).sum := by decide
  have hdescent : baseEnd_4186220 < baseStart_4186220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186230 : List Nat := [5, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2]
def baseStart_4186230 : Nat := 118140960795 + 4186230 * 2 ^ 59
def prefixEnd_4186230 : Nat := 4983230072969 + 3 ^ 40 * 4186230 * 2
def baseEnd_4186230 : Nat := 2149548120271261589572885

theorem tailTrace_4186230 : CollatzResearch.WordTrace tailWord_4186230 prefixEnd_4186230 2149548120271261589572885 := by
  unfold tailWord_4186230
  simp only [CollatzResearch.WordTrace]
  refine ⟨9542771976500696000558759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101789567749340757339293429 9542771976500696000558759)
  ·
    refine ⟨14314157964751044000838139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9542771976500696000558759 14314157964751044000838139)
    ·
      refine ⟨21471236947126566001257209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14314157964751044000838139 21471236947126566001257209)
      ·
        refine ⟨16103427710344924500942907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21471236947126566001257209 16103427710344924500942907)
        ·
          refine ⟨24155141565517386751414361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16103427710344924500942907 24155141565517386751414361)
          ·
            refine ⟨18116356174138040063560771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24155141565517386751414361 18116356174138040063560771)
            ·
              refine ⟨27174534261207060095341157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18116356174138040063560771 27174534261207060095341157)
              ·
                refine ⟨5095225173976323767876467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27174534261207060095341157 5095225173976323767876467)
                ·
                  refine ⟨7642837760964485651814701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095225173976323767876467 7642837760964485651814701)
                  ·
                    refine ⟨2866064160361682119430513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7642837760964485651814701 2866064160361682119430513)
                    ·
                      refine ⟨2149548120271261589572885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2866064160361682119430513 2149548120271261589572885)
                      ·
                        rfl

theorem cell23_4186230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_4186230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186230 prefixEnd_4186230 := by exact prefixLift 4186230
  have htrace : WordTrace (prefixWord ++ tailWord_4186230) baseStart_4186230 baseEnd_4186230 := by
    simpa [prefixWord, tailWord_4186230, baseEnd_4186230] using wordTrace_append hprefix tailTrace_4186230
  have hstable : (prefixWord ++ tailWord_4186230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186230).length < 2 ^ (prefixWord ++ tailWord_4186230).sum := by decide
  have hdescent : baseEnd_4186230 < baseStart_4186230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186243 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 4, 2, 2]
def baseStart_4186243 : Nat := 118140960795 + 4186243 * 2 ^ 59
def prefixEnd_4186243 : Nat := 4983230072969 + 3 ^ 40 * 4186243 * 2
def baseEnd_4186243 : Nat := 2149554795519770038710325

theorem tailTrace_4186243 : CollatzResearch.WordTrace tailWord_4186243 prefixEnd_4186243 2149554795519770038710325 := by
  unfold tailWord_4186243
  simp only [CollatzResearch.WordTrace]
  refine ⟨152684825772964039229163383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101789883848642692819442255 152684825772964039229163383)
  ·
    refine ⟨229027238659446058843745075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152684825772964039229163383 229027238659446058843745075)
    ·
      refine ⟨343540857989169088265617613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229027238659446058843745075 343540857989169088265617613)
      ·
        refine ⟨128827821745938408099606605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343540857989169088265617613 128827821745938408099606605)
        ·
          refine ⟨48310433154726903037352477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128827821745938408099606605 48310433154726903037352477)
          ·
            refine ⟨18116412433022588639007179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48310433154726903037352477 18116412433022588639007179)
            ·
              refine ⟨27174618649533882958510769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18116412433022588639007179 27174618649533882958510769)
              ·
                refine ⟨20380963987150412218883077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27174618649533882958510769 20380963987150412218883077)
                ·
                  refine ⟨3821430747590702291040577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20380963987150412218883077 3821430747590702291040577)
                  ·
                    refine ⟨2866073060693026718280433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3821430747590702291040577 2866073060693026718280433)
                    ·
                      refine ⟨2149554795519770038710325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2866073060693026718280433 2149554795519770038710325)
                      ·
                        rfl

theorem cell23_4186243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 2, 2].length) (baseStart_4186243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186243 prefixEnd_4186243 := by exact prefixLift 4186243
  have htrace : WordTrace (prefixWord ++ tailWord_4186243) baseStart_4186243 baseEnd_4186243 := by
    simpa [prefixWord, tailWord_4186243, baseEnd_4186243] using wordTrace_append hprefix tailTrace_4186243
  have hstable : (prefixWord ++ tailWord_4186243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186243).length < 2 ^ (prefixWord ++ tailWord_4186243).sum := by decide
  have hdescent : baseEnd_4186243 < baseStart_4186243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186296 : List Nat := [2, 1, 2, 1, 2, 1, 6, 1, 2, 5]
def baseStart_4186296 : Nat := 118140960795 + 4186296 * 2 ^ 59
def prefixEnd_4186296 : Nat := 4983230072969 + 3 ^ 40 * 4186296 * 2
def baseEnd_4186296 : Nat := 716527336664819443782527

theorem tailTrace_4186296 : CollatzResearch.WordTrace tailWord_4186296 prefixEnd_4186296 716527336664819443782527 := by
  unfold tailWord_4186296
  simp only [CollatzResearch.WordTrace]
  refine ⟨76343379420886014640421371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101791172561181352853895161 76343379420886014640421371)
  ·
    refine ⟨114515069131329021960632057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76343379420886014640421371 114515069131329021960632057)
    ·
      refine ⟨85886301848496766470474043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114515069131329021960632057 85886301848496766470474043)
      ·
        refine ⟨128829452772745149705711065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85886301848496766470474043 128829452772745149705711065)
        ·
          refine ⟨96622089579558862279283299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128829452772745149705711065 96622089579558862279283299)
          ·
            refine ⟨144933134369338293418924949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96622089579558862279283299 144933134369338293418924949)
            ·
              refine ⟨6793740673562732504012107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144933134369338293418924949 6793740673562732504012107)
              ·
                refine ⟨10190611010344098756018161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6793740673562732504012107 10190611010344098756018161)
                ·
                  refine ⟨7642958257758074067013621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10190611010344098756018161 7642958257758074067013621)
                  ·
                    refine ⟨716527336664819443782527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7642958257758074067013621 716527336664819443782527)
                    ·
                      rfl

theorem cell23_4186296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_4186296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186296 prefixEnd_4186296 := by exact prefixLift 4186296
  have htrace : WordTrace (prefixWord ++ tailWord_4186296) baseStart_4186296 baseEnd_4186296 := by
    simpa [prefixWord, tailWord_4186296, baseEnd_4186296] using wordTrace_append hprefix tailTrace_4186296
  have hstable : (prefixWord ++ tailWord_4186296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186296).length < 2 ^ (prefixWord ++ tailWord_4186296).sum := by decide
  have hdescent : baseEnd_4186296 < baseStart_4186296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186319 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 5]
def baseStart_4186319 : Nat := 118140960795 + 4186319 * 2 ^ 59
def prefixEnd_4186319 : Nat := 4983230072969 + 3 ^ 40 * 4186319 * 2
def baseEnd_4186319 : Nat := 2149593820049511741359975

theorem tailTrace_4186319 : CollatzResearch.WordTrace tailWord_4186319 prefixEnd_4186319 2149593820049511741359975 := by
  unfold tailWord_4186319
  simp only [CollatzResearch.WordTrace]
  refine ⟨152687597720688704208930011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101791731813792469472620007 152687597720688704208930011)
  ·
    refine ⟨229031396581033056313395017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152687597720688704208930011 229031396581033056313395017)
    ·
      refine ⟨171773547435774792235046263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229031396581033056313395017 171773547435774792235046263)
      ·
        refine ⟨257660321153662188352569395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171773547435774792235046263 257660321153662188352569395)
        ·
          refine ⟨386490481730493282528854093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257660321153662188352569395 386490481730493282528854093)
          ·
            refine ⟨144933930648934980948320285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386490481730493282528854093 144933930648934980948320285)
            ·
              refine ⟨54350223993350617855620107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144933930648934980948320285 54350223993350617855620107)
              ·
                refine ⟨81525335990025926783430161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54350223993350617855620107 81525335990025926783430161)
                ·
                  refine ⟨61144001992519445087572621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81525335990025926783430161 61144001992519445087572621)
                  ·
                    refine ⟨22929000747194791907839733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61144001992519445087572621 22929000747194791907839733)
                    ·
                      refine ⟨2149593820049511741359975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22929000747194791907839733 2149593820049511741359975)
                      ·
                        rfl

theorem cell23_4186319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_4186319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186319 prefixEnd_4186319 := by exact prefixLift 4186319
  have htrace : WordTrace (prefixWord ++ tailWord_4186319) baseStart_4186319 baseEnd_4186319 := by
    simpa [prefixWord, tailWord_4186319, baseEnd_4186319] using wordTrace_append hprefix tailTrace_4186319
  have hstable : (prefixWord ++ tailWord_4186319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186319).length < 2 ^ (prefixWord ++ tailWord_4186319).sum := by decide
  have hdescent : baseEnd_4186319 < baseStart_4186319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186336 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 3]
def baseStart_4186336 : Nat := 118140960795 + 4186336 * 2 ^ 59
def prefixEnd_4186336 : Nat := 4983230072969 + 3 ^ 40 * 4186336 * 2
def baseEnd_4186336 : Nat := 2149602549220638174847397

theorem tailTrace_4186336 : CollatzResearch.WordTrace tailWord_4186336 prefixEnd_4186336 2149602549220638174847397 := by
  unfold tailWord_4186336
  simp only [CollatzResearch.WordTrace]
  refine ⟨76344108880813558056149431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101792145174418077408199241 76344108880813558056149431)
  ·
    refine ⟨114516163321220337084224147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76344108880813558056149431 114516163321220337084224147)
    ·
      refine ⟨171774244981830505626336221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114516163321220337084224147 171774244981830505626336221)
      ·
        refine ⟨64415341868186439609876083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171774244981830505626336221 64415341868186439609876083)
        ·
          refine ⟨96623012802279659414814125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64415341868186439609876083 96623012802279659414814125)
          ·
            refine ⟨36233629800854872280555297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96623012802279659414814125 36233629800854872280555297)
            ·
              refine ⟨27175222350641154210416473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36233629800854872280555297 27175222350641154210416473)
              ·
                refine ⟨20381416762980865657812355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27175222350641154210416473 20381416762980865657812355)
                ·
                  refine ⟨30572125144471298486718533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20381416762980865657812355 30572125144471298486718533)
                  ·
                    refine ⟨5732273464588368466259725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30572125144471298486718533 5732273464588368466259725)
                    ·
                      refine ⟨2149602549220638174847397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5732273464588368466259725 2149602549220638174847397)
                      ·
                        rfl

theorem cell23_4186336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_4186336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186336 prefixEnd_4186336 := by exact prefixLift 4186336
  have htrace : WordTrace (prefixWord ++ tailWord_4186336) baseStart_4186336 baseEnd_4186336 := by
    simpa [prefixWord, tailWord_4186336, baseEnd_4186336] using wordTrace_append hprefix tailTrace_4186336
  have hstable : (prefixWord ++ tailWord_4186336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186336).length < 2 ^ (prefixWord ++ tailWord_4186336).sum := by decide
  have hdescent : baseEnd_4186336 < baseStart_4186336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186343 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 5, 4]
def baseStart_4186343 : Nat := 118140960795 + 4186343 * 2 ^ 59
def prefixEnd_4186343 : Nat := 4983230072969 + 3 ^ 40 * 4186343 * 2
def baseEnd_4186343 : Nat := 716535381195073215819955

theorem tailTrace_4186343 : CollatzResearch.WordTrace tailWord_4186343 prefixEnd_4186343 716535381195073215819955 := by
  unfold tailWord_4186343
  simp only [CollatzResearch.WordTrace]
  refine ⟨152688473072601756307803683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101792315381734504205202455 152688473072601756307803683)
  ·
    refine ⟨229032709608902634461705525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152688473072601756307803683 229032709608902634461705525)
    ·
      refine ⟨21471816525834621980784893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 229032709608902634461705525 21471816525834621980784893)
      ·
        refine ⟨8051931197187983242794335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21471816525834621980784893 8051931197187983242794335)
        ·
          refine ⟨12077896795781974864191503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8051931197187983242794335 12077896795781974864191503)
          ·
            refine ⟨18116845193672962296287255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12077896795781974864191503 18116845193672962296287255)
            ·
              refine ⟨27175267790509443444430883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18116845193672962296287255 27175267790509443444430883)
              ·
                refine ⟨40762901685764165166646325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27175267790509443444430883 40762901685764165166646325)
                ·
                  refine ⟨3821522033040390484373093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40762901685764165166646325 3821522033040390484373093)
                  ·
                    refine ⟨716535381195073215819955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3821522033040390484373093 716535381195073215819955)
                    ·
                      rfl

theorem cell23_4186343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_4186343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186343 prefixEnd_4186343 := by exact prefixLift 4186343
  have htrace : WordTrace (prefixWord ++ tailWord_4186343) baseStart_4186343 baseEnd_4186343 := by
    simpa [prefixWord, tailWord_4186343, baseEnd_4186343] using wordTrace_append hprefix tailTrace_4186343
  have hstable : (prefixWord ++ tailWord_4186343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186343).length < 2 ^ (prefixWord ++ tailWord_4186343).sum := by decide
  have hdescent : baseEnd_4186343 < baseStart_4186343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186353 : List Nat := [1, 2, 2, 2, 2, 1, 5, 1, 2, 2, 3]
def baseStart_4186353 : Nat := 118140960795 + 4186353 * 2 ^ 59
def prefixEnd_4186353 : Nat := 4983230072969 + 3 ^ 40 * 4186353 * 2
def baseEnd_4186353 : Nat := 2149611278391764608334819

theorem tailTrace_4186353 : CollatzResearch.WordTrace tailWord_4186353 prefixEnd_4186353 2149611278391764608334819 := by
  unfold tailWord_4186353
  simp only [CollatzResearch.WordTrace]
  refine ⟨152688837802565528015667713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101792558535043685343778475 152688837802565528015667713)
  ·
    refine ⟨114516628351924146011750785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152688837802565528015667713 114516628351924146011750785)
    ·
      refine ⟨85887471263943109508813089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114516628351924146011750785 85887471263943109508813089)
      ·
        refine ⟨64415603447957332131609817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85887471263943109508813089 64415603447957332131609817)
        ·
          refine ⟨48311702585967999098707363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64415603447957332131609817 48311702585967999098707363)
          ·
            refine ⟨72467553878951998648061045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48311702585967999098707363 72467553878951998648061045)
            ·
              refine ⟨6793833176151749873255723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72467553878951998648061045 6793833176151749873255723)
              ·
                refine ⟨10190749764227624809883585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6793833176151749873255723 10190749764227624809883585)
                ·
                  refine ⟨7643062323170718607412689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10190749764227624809883585 7643062323170718607412689)
                  ·
                    refine ⟨5732296742378038955559517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7643062323170718607412689 5732296742378038955559517)
                    ·
                      refine ⟨2149611278391764608334819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5732296742378038955559517 2149611278391764608334819)
                      ·
                        rfl

theorem cell23_4186353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_4186353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186353 prefixEnd_4186353 := by exact prefixLift 4186353
  have htrace : WordTrace (prefixWord ++ tailWord_4186353) baseStart_4186353 baseEnd_4186353 := by
    simpa [prefixWord, tailWord_4186353, baseEnd_4186353] using wordTrace_append hprefix tailTrace_4186353
  have hstable : (prefixWord ++ tailWord_4186353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186353).length < 2 ^ (prefixWord ++ tailWord_4186353).sum := by decide
  have hdescent : baseEnd_4186353 < baseStart_4186353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186359 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 8]
def baseStart_4186359 : Nat := 118140960795 + 4186359 * 2 ^ 59
def prefixEnd_4186359 : Nat := 4983230072969 + 3 ^ 40 * 4186359 * 2
def baseEnd_4186359 : Nat := 2149614359275691584859791

theorem tailTrace_4186359 : CollatzResearch.WordTrace tailWord_4186359 prefixEnd_4186359 2149614359275691584859791 := by
  unfold tailWord_4186359
  simp only [CollatzResearch.WordTrace]
  refine ⟨152689056640543791040386131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101792704427029194026924087 152689056640543791040386131)
  ·
    refine ⟨229033584960815686560579197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152689056640543791040386131 229033584960815686560579197)
    ·
      refine ⟨85887594360305882460217199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229033584960815686560579197 85887594360305882460217199)
      ·
        refine ⟨128831391540458823690325799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85887594360305882460217199 128831391540458823690325799)
        ·
          refine ⟨193247087310688235535488699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128831391540458823690325799 193247087310688235535488699)
          ·
            refine ⟨289870630966032353303233049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193247087310688235535488699 289870630966032353303233049)
            ·
              refine ⟨217402973224524264977424787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289870630966032353303233049 217402973224524264977424787)
              ·
                refine ⟨326104459836786397466137181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217402973224524264977424787 326104459836786397466137181)
                ·
                  refine ⟨122289172438794899049801443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326104459836786397466137181 122289172438794899049801443)
                  ·
                    refine ⟨183433758658192348574702165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122289172438794899049801443 183433758658192348574702165)
                    ·
                      refine ⟨2149614359275691584859791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 183433758658192348574702165 2149614359275691584859791)
                      ·
                        rfl

theorem cell23_4186359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_4186359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186359 prefixEnd_4186359 := by exact prefixLift 4186359
  have htrace : WordTrace (prefixWord ++ tailWord_4186359) baseStart_4186359 baseEnd_4186359 := by
    simpa [prefixWord, tailWord_4186359, baseEnd_4186359] using wordTrace_append hprefix tailTrace_4186359
  have hstable : (prefixWord ++ tailWord_4186359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186359).length < 2 ^ (prefixWord ++ tailWord_4186359).sum := by decide
  have hdescent : baseEnd_4186359 < baseStart_4186359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186376 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_4186376 : Nat := 118140960795 + 4186376 * 2 ^ 59
def prefixEnd_4186376 : Nat := 4983230072969 + 3 ^ 40 * 4186376 * 2
def baseEnd_4186376 : Nat := 2149623088446818018347213

theorem tailTrace_4186376 : CollatzResearch.WordTrace tailWord_4186376 prefixEnd_4186376 2149623088446818018347213 := by
  unfold tailWord_4186376
  simp only [CollatzResearch.WordTrace]
  refine ⟨76344838340741101471877491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101793117787654801962503321 76344838340741101471877491)
  ·
    refine ⟨114517257511111652207816237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76344838340741101471877491 114517257511111652207816237)
    ·
      refine ⟨42943971566666869577931089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114517257511111652207816237 42943971566666869577931089)
      ·
        refine ⟨32207978675000152183448317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42943971566666869577931089 32207978675000152183448317)
        ·
          refine ⟨12077992003125057068793119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32207978675000152183448317 12077992003125057068793119)
          ·
            refine ⟨18116988004687585603189679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12077992003125057068793119 18116988004687585603189679)
            ·
              refine ⟨27175482007031378404784519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18116988004687585603189679 27175482007031378404784519)
              ·
                refine ⟨40763223010547067607176779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27175482007031378404784519 40763223010547067607176779)
                ·
                  refine ⟨61144834515820601410765169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40763223010547067607176779 61144834515820601410765169)
                  ·
                    refine ⟨45858625886865451058073877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61144834515820601410765169 45858625886865451058073877)
                    ·
                      refine ⟨2149623088446818018347213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45858625886865451058073877 2149623088446818018347213)
                      ·
                        rfl

theorem cell23_4186376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_4186376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186376 prefixEnd_4186376 := by exact prefixLift 4186376
  have htrace : WordTrace (prefixWord ++ tailWord_4186376) baseStart_4186376 baseEnd_4186376 := by
    simpa [prefixWord, tailWord_4186376, baseEnd_4186376] using wordTrace_append hprefix tailTrace_4186376
  have hstable : (prefixWord ++ tailWord_4186376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186376).length < 2 ^ (prefixWord ++ tailWord_4186376).sum := by decide
  have hdescent : baseEnd_4186376 < baseStart_4186376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186400 : List Nat := [2, 1, 1, 5, 2, 1, 2, 2, 3, 1, 3]
def baseStart_4186400 : Nat := 118140960795 + 4186400 * 2 ^ 59
def prefixEnd_4186400 : Nat := 4983230072969 + 3 ^ 40 * 4186400 * 2
def baseEnd_4186400 : Nat := 2149635411982525924447103

theorem tailTrace_4186400 : CollatzResearch.WordTrace tailWord_4186400 prefixEnd_4186400 2149635411982525924447103 := by
  unfold tailWord_4186400
  simp only [CollatzResearch.WordTrace]
  refine ⟨76345276016697627521314327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101793701355596836695085769 76345276016697627521314327)
  ·
    refine ⟨114517914025046441281971491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76345276016697627521314327 114517914025046441281971491)
    ·
      refine ⟨171776871037569661922957237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114517914025046441281971491 171776871037569661922957237)
      ·
        refine ⟨16104081659772155805277241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171776871037569661922957237 16104081659772155805277241)
        ·
          refine ⟨12078061244829116853957931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16104081659772155805277241 12078061244829116853957931)
          ·
            refine ⟨18117091867243675280936897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12078061244829116853957931 18117091867243675280936897)
            ·
              refine ⟨13587818900432756460702673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18117091867243675280936897 13587818900432756460702673)
              ·
                refine ⟨10190864175324567345527005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13587818900432756460702673 10190864175324567345527005)
                ·
                  refine ⟨3821574065746712754572627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10190864175324567345527005 3821574065746712754572627)
                  ·
                    refine ⟨5732361098620069131858941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3821574065746712754572627 5732361098620069131858941)
                    ·
                      refine ⟨2149635411982525924447103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5732361098620069131858941 2149635411982525924447103)
                      ·
                        rfl

theorem cell23_4186400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_4186400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186400 prefixEnd_4186400 := by exact prefixLift 4186400
  have htrace : WordTrace (prefixWord ++ tailWord_4186400) baseStart_4186400 baseEnd_4186400 := by
    simpa [prefixWord, tailWord_4186400, baseEnd_4186400] using wordTrace_append hprefix tailTrace_4186400
  have hstable : (prefixWord ++ tailWord_4186400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186400).length < 2 ^ (prefixWord ++ tailWord_4186400).sum := by decide
  have hdescent : baseEnd_4186400 < baseStart_4186400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186403 : List Nat := [1, 1, 1, 4, 2, 2, 4, 2, 1, 5]
def baseStart_4186403 : Nat := 118140960795 + 4186403 * 2 ^ 59
def prefixEnd_4186403 : Nat := 4983230072969 + 3 ^ 40 * 4186403 * 2
def baseEnd_4186403 : Nat := 716545650808163137569863

theorem tailTrace_4186403 : CollatzResearch.WordTrace tailWord_4186403 prefixEnd_4186403 716545650808163137569863 := by
  unfold tailWord_4186403
  simp only [CollatzResearch.WordTrace]
  refine ⟨152690661452384386554987863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101793774301589591036658575 152690661452384386554987863)
  ·
    refine ⟨229035992178576579832481795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152690661452384386554987863 229035992178576579832481795)
    ·
      refine ⟨343553988267864869748722693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229035992178576579832481795 343553988267864869748722693)
      ·
        refine ⟨64416372800224663077885505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343553988267864869748722693 64416372800224663077885505)
        ·
          refine ⟨48312279600168497308414129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64416372800224663077885505 48312279600168497308414129)
          ·
            refine ⟨36234209700126372981310597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48312279600168497308414129 36234209700126372981310597)
            ·
              refine ⟨6793914318773694933995737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36234209700126372981310597 6793914318773694933995737)
              ·
                refine ⟨5095435739080271200496803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6793914318773694933995737 5095435739080271200496803)
                ·
                  refine ⟨7643153608620406800745205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095435739080271200496803 7643153608620406800745205)
                  ·
                    refine ⟨716545650808163137569863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7643153608620406800745205 716545650808163137569863)
                    ·
                      rfl

theorem cell23_4186403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 5].length) (baseStart_4186403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186403 prefixEnd_4186403 := by exact prefixLift 4186403
  have htrace : WordTrace (prefixWord ++ tailWord_4186403) baseStart_4186403 baseEnd_4186403 := by
    simpa [prefixWord, tailWord_4186403, baseEnd_4186403] using wordTrace_append hprefix tailTrace_4186403
  have hstable : (prefixWord ++ tailWord_4186403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186403).length < 2 ^ (prefixWord ++ tailWord_4186403).sum := by decide
  have hdescent : baseEnd_4186403 < baseStart_4186403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186420 : List Nat := [2, 5, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_4186420 : Nat := 118140960795 + 4186420 * 2 ^ 59
def prefixEnd_4186420 : Nat := 4983230072969 + 3 ^ 40 * 4186420 * 2
def baseEnd_4186420 : Nat := 716548560531871948732337

theorem tailTrace_4186420 : CollatzResearch.WordTrace tailWord_4186420 prefixEnd_4186420 716548560531871948732337 := by
  unfold tailWord_4186420
  simp only [CollatzResearch.WordTrace]
  refine ⟨76345640746661399229178357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101794187662215198972237809 76345640746661399229178357)
  ·
    refine ⟨7157403819999506177735471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76345640746661399229178357 7157403819999506177735471)
    ·
      refine ⟨10736105729999259266603207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7157403819999506177735471 10736105729999259266603207)
      ·
        refine ⟨16104158594998888899904811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10736105729999259266603207 16104158594998888899904811)
        ·
          refine ⟨24156237892498333349857217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16104158594998888899904811 24156237892498333349857217)
          ·
            refine ⟨18117178419373750012392913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24156237892498333349857217 18117178419373750012392913)
            ·
              refine ⟨13587883814530312509294685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18117178419373750012392913 13587883814530312509294685)
              ·
                refine ⟨5095456430448867190985507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13587883814530312509294685 5095456430448867190985507)
                ·
                  refine ⟨7643184645673300786478261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095456430448867190985507 7643184645673300786478261)
                  ·
                    refine ⟨716548560531871948732337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7643184645673300786478261 716548560531871948732337)
                    ·
                      rfl

theorem cell23_4186420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_4186420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186420 prefixEnd_4186420 := by exact prefixLift 4186420
  have htrace : WordTrace (prefixWord ++ tailWord_4186420) baseStart_4186420 baseEnd_4186420 := by
    simpa [prefixWord, tailWord_4186420, baseEnd_4186420] using wordTrace_append hprefix tailTrace_4186420
  have hstable : (prefixWord ++ tailWord_4186420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186420).length < 2 ^ (prefixWord ++ tailWord_4186420).sum := by decide
  have hdescent : baseEnd_4186420 < baseStart_4186420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186473 : List Nat := [1, 2, 1, 1, 1, 3, 5, 2, 1, 3, 3]
def baseStart_4186473 : Nat := 118140960795 + 4186473 * 2 ^ 59
def prefixEnd_4186473 : Nat := 4983230072969 + 3 ^ 40 * 4186473 * 2
def baseEnd_4186473 : Nat := 2149672896070304138834267

theorem tailTrace_4186473 : CollatzResearch.WordTrace tailWord_4186473 prefixEnd_4186473 2149672896070304138834267 := by
  unfold tailWord_4186473
  simp only [CollatzResearch.WordTrace]
  refine ⟨152693214562130788510036073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101795476374753859006690715 152693214562130788510036073)
  ·
    refine ⟨114519910921598091382527055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152693214562130788510036073 114519910921598091382527055)
    ·
      refine ⟨171779866382397137073790583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114519910921598091382527055 171779866382397137073790583)
      ·
        refine ⟨257669799573595705610685875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171779866382397137073790583 257669799573595705610685875)
        ·
          refine ⟨386504699360393558416028813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257669799573595705610685875 386504699360393558416028813)
          ·
            refine ⟨144939262260147584406010805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386504699360393558416028813 144939262260147584406010805)
            ·
              refine ⟨13588055836888836038063513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144939262260147584406010805 13588055836888836038063513)
              ·
                refine ⟨10191041877666627028547635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13588055836888836038063513 10191041877666627028547635)
                ·
                  refine ⟨15286562816499940542821453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10191041877666627028547635 15286562816499940542821453)
                  ·
                    refine ⟨5732461056187477703558045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15286562816499940542821453 5732461056187477703558045)
                    ·
                      refine ⟨2149672896070304138834267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5732461056187477703558045 2149672896070304138834267)
                      ·
                        rfl

theorem cell23_4186473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 3, 3].length) (baseStart_4186473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186473 prefixEnd_4186473 := by exact prefixLift 4186473
  have htrace : WordTrace (prefixWord ++ tailWord_4186473) baseStart_4186473 baseEnd_4186473 := by
    simpa [prefixWord, tailWord_4186473, baseEnd_4186473] using wordTrace_append hprefix tailTrace_4186473
  have hstable : (prefixWord ++ tailWord_4186473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186473).length < 2 ^ (prefixWord ++ tailWord_4186473).sum := by decide
  have hdescent : baseEnd_4186473 < baseStart_4186473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186477 : List Nat := [1, 5, 1, 1, 1, 2, 5, 1, 1, 2, 3]
def baseStart_4186477 : Nat := 118140960795 + 4186477 * 2 ^ 59
def prefixEnd_4186477 : Nat := 4983230072969 + 3 ^ 40 * 4186477 * 2
def baseEnd_4186477 : Nat := 2149674949992922123184249

theorem tailTrace_4186477 : CollatzResearch.WordTrace tailWord_4186477 prefixEnd_4186477 2149674949992922123184249 := by
  unfold tailWord_4186477
  simp only [CollatzResearch.WordTrace]
  refine ⟨152693360454116297193181685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101795573636077531462121123 152693360454116297193181685)
  ·
    refine ⟨14315002542573402861860783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152693360454116297193181685 14315002542573402861860783)
    ·
      refine ⟨21472503813860104292791175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14315002542573402861860783 21472503813860104292791175)
      ·
        refine ⟨32208755720790156439186763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21472503813860104292791175 32208755720790156439186763)
        ·
          refine ⟨48313133581185234658780145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32208755720790156439186763 48313133581185234658780145)
          ·
            refine ⟨36234850185888925994085109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48313133581185234658780145 36234850185888925994085109)
            ·
              refine ⟨3397017204927086811945479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36234850185888925994085109 3397017204927086811945479)
              ·
                refine ⟨5095525807390630217918219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3397017204927086811945479 5095525807390630217918219)
                ·
                  refine ⟨7643288711085945326877329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095525807390630217918219 7643288711085945326877329)
                  ·
                    refine ⟨5732466533314458995157997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7643288711085945326877329 5732466533314458995157997)
                    ·
                      refine ⟨2149674949992922123184249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5732466533314458995157997 2149674949992922123184249)
                      ·
                        rfl

theorem cell23_4186477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_4186477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186477 prefixEnd_4186477 := by exact prefixLift 4186477
  have htrace : WordTrace (prefixWord ++ tailWord_4186477) baseStart_4186477 baseEnd_4186477 := by
    simpa [prefixWord, tailWord_4186477, baseEnd_4186477] using wordTrace_append hprefix tailTrace_4186477
  have hstable : (prefixWord ++ tailWord_4186477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186477).length < 2 ^ (prefixWord ++ tailWord_4186477).sum := by decide
  have hdescent : baseEnd_4186477 < baseStart_4186477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186491 : List Nat := [1, 1, 1, 1, 1, 9, 2, 2, 1, 2, 2]
def baseStart_4186491 : Nat := 118140960795 + 4186491 * 2 ^ 59
def prefixEnd_4186491 : Nat := 4983230072969 + 3 ^ 40 * 4186491 * 2
def baseEnd_4186491 : Nat := 2149682138722085068409185

theorem tailTrace_4186491 : CollatzResearch.WordTrace tailWord_4186491 prefixEnd_4186491 2149682138722085068409185 := by
  unfold tailWord_4186491
  simp only [CollatzResearch.WordTrace]
  refine ⟨152693871076065577584191327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101795914050710385056127551 152693871076065577584191327)
  ·
    refine ⟨229040806614098366376286991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152693871076065577584191327 229040806614098366376286991)
    ·
      refine ⟨343561209921147549564430487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229040806614098366376286991 343561209921147549564430487)
      ·
        refine ⟨515341814881721324346645731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343561209921147549564430487 515341814881721324346645731)
        ·
          refine ⟨773012722322581986519968597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515341814881721324346645731 773012722322581986519968597)
          ·
            refine ⟨4529371419858878827265441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 773012722322581986519968597 4529371419858878827265441)
            ·
              refine ⟨3397028564894159120449081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4529371419858878827265441 3397028564894159120449081)
              ·
                refine ⟨2547771423670619340336811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3397028564894159120449081 2547771423670619340336811)
                ·
                  refine ⟨3821657135505929010505217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2547771423670619340336811 3821657135505929010505217)
                  ·
                    refine ⟨2866242851629446757878913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3821657135505929010505217 2866242851629446757878913)
                    ·
                      refine ⟨2149682138722085068409185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2866242851629446757878913 2149682138722085068409185)
                      ·
                        rfl

theorem cell23_4186491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 1, 2, 2].length) (baseStart_4186491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186491 prefixEnd_4186491 := by exact prefixLift 4186491
  have htrace : WordTrace (prefixWord ++ tailWord_4186491) baseStart_4186491 baseEnd_4186491 := by
    simpa [prefixWord, tailWord_4186491, baseEnd_4186491] using wordTrace_append hprefix tailTrace_4186491
  have hstable : (prefixWord ++ tailWord_4186491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186491).length < 2 ^ (prefixWord ++ tailWord_4186491).sum := by decide
  have hdescent : baseEnd_4186491 < baseStart_4186491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186500 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 5, 3, 2]
def baseStart_4186500 : Nat := 118140960795 + 4186500 * 2 ^ 59
def prefixEnd_4186500 : Nat := 4983230072969 + 3 ^ 40 * 4186500 * 2
def baseEnd_4186500 : Nat := 2149686760047975533196643

theorem tailTrace_4186500 : CollatzResearch.WordTrace tailWord_4186500 prefixEnd_4186500 2149686760047975533196643 := by
  unfold tailWord_4186500
  simp only [CollatzResearch.WordTrace]
  refine ⟨76347099666516486060634477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101796132888688648080845969 76347099666516486060634477)
  ·
    refine ⟨28630162374943682272737929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76347099666516486060634477 28630162374943682272737929)
    ·
      refine ⟨21472621781207761704553447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28630162374943682272737929 21472621781207761704553447)
      ·
        refine ⟨32208932671811642556830171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21472621781207761704553447 32208932671811642556830171)
        ·
          refine ⟨48313399007717463835245257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32208932671811642556830171 48313399007717463835245257)
          ·
            refine ⟨36235049255788097876433943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48313399007717463835245257 36235049255788097876433943)
            ·
              refine ⟨54352573883682146814650915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36235049255788097876433943 54352573883682146814650915)
              ·
                refine ⟨81528860825523220221976373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54352573883682146814650915 81528860825523220221976373)
                ·
                  refine ⟨7643330702392801895810285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81528860825523220221976373 7643330702392801895810285)
                  ·
                    refine ⟨2866249013397300710928857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7643330702392801895810285 2866249013397300710928857)
                    ·
                      refine ⟨2149686760047975533196643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2866249013397300710928857 2149686760047975533196643)
                      ·
                        rfl

theorem cell23_4186500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_4186500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186500 prefixEnd_4186500 := by exact prefixLift 4186500
  have htrace : WordTrace (prefixWord ++ tailWord_4186500) baseStart_4186500 baseEnd_4186500 := by
    simpa [prefixWord, tailWord_4186500, baseEnd_4186500] using wordTrace_append hprefix tailTrace_4186500
  have hstable : (prefixWord ++ tailWord_4186500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186500).length < 2 ^ (prefixWord ++ tailWord_4186500).sum := by decide
  have hdescent : baseEnd_4186500 < baseStart_4186500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186541 : List Nat := [1, 5, 2, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_4186541 : Nat := 118140960795 + 4186541 * 2 ^ 59
def prefixEnd_4186541 : Nat := 4983230072969 + 3 ^ 40 * 4186541 * 2
def baseEnd_4186541 : Nat := 2149707812754809872783955

theorem tailTrace_4186541 : CollatzResearch.WordTrace tailWord_4186541 prefixEnd_4186541 2149707812754809872783955 := by
  unfold tailWord_4186541
  simp only [CollatzResearch.WordTrace]
  refine ⟨152695694725884436123511477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101797129817256290749007651 152695694725884436123511477)
  ·
    refine ⟨14315221380551665886579201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152695694725884436123511477 14315221380551665886579201)
    ·
      refine ⟨10736416035413749414934401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14315221380551665886579201 10736416035413749414934401)
      ·
        refine ⟨8052312026560312061200801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10736416035413749414934401 8052312026560312061200801)
        ·
          refine ⟨6039234019920234045900601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8052312026560312061200801 6039234019920234045900601)
          ·
            refine ⟨4529425514940175534425451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6039234019920234045900601 4529425514940175534425451)
            ·
              refine ⟨6794138272410263301638177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4529425514940175534425451 6794138272410263301638177)
              ·
                refine ⟨5095603704307697476228633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6794138272410263301638177 5095603704307697476228633)
                ·
                  refine ⟨3821702778230773107171475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5095603704307697476228633 3821702778230773107171475)
                  ·
                    refine ⟨5732554167346159660757213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3821702778230773107171475 5732554167346159660757213)
                    ·
                      refine ⟨2149707812754809872783955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5732554167346159660757213 2149707812754809872783955)
                      ·
                        rfl

theorem cell23_4186541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_4186541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186541 prefixEnd_4186541 := by exact prefixLift 4186541
  have htrace : WordTrace (prefixWord ++ tailWord_4186541) baseStart_4186541 baseEnd_4186541 := by
    simpa [prefixWord, tailWord_4186541, baseEnd_4186541] using wordTrace_append hprefix tailTrace_4186541
  have hstable : (prefixWord ++ tailWord_4186541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186541).length < 2 ^ (prefixWord ++ tailWord_4186541).sum := by decide
  have hdescent : baseEnd_4186541 < baseStart_4186541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186553 : List Nat := [1, 2, 1, 4, 3, 1, 1, 3, 7]
def baseStart_4186553 : Nat := 118140960795 + 4186553 * 2 ^ 59
def prefixEnd_4186553 : Nat := 4983230072969 + 3 ^ 40 * 4186553 * 2
def baseEnd_4186553 : Nat := 238857108280295980648211

theorem tailTrace_4186553 : CollatzResearch.WordTrace tailWord_4186553 prefixEnd_4186553 238857108280295980648211 := by
  unfold tailWord_4186553
  simp only [CollatzResearch.WordTrace]
  refine ⟨152696132401840962172948313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101797421601227308115298875 152696132401840962172948313)
  ·
    refine ⟨114522099301380721629711235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152696132401840962172948313 114522099301380721629711235)
    ·
      refine ⟨171783148952071082444566853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114522099301380721629711235 171783148952071082444566853)
      ·
        refine ⟨32209340428513327958356285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171783148952071082444566853 32209340428513327958356285)
        ·
          refine ⟨12078502660692497984383607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32209340428513327958356285 12078502660692497984383607)
          ·
            refine ⟨18117753991038746976575411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12078502660692497984383607 18117753991038746976575411)
            ·
              refine ⟨27176630986558120464863117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18117753991038746976575411 27176630986558120464863117)
              ·
                refine ⟨10191236619959295174323669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27176630986558120464863117 10191236619959295174323669)
                ·
                  refine ⟨238857108280295980648211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10191236619959295174323669 238857108280295980648211)
                  ·
                    rfl

theorem cell23_4186553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 7].length) (baseStart_4186553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186553 prefixEnd_4186553 := by exact prefixLift 4186553
  have htrace : WordTrace (prefixWord ++ tailWord_4186553) baseStart_4186553 baseEnd_4186553 := by
    simpa [prefixWord, tailWord_4186553, baseEnd_4186553] using wordTrace_append hprefix tailTrace_4186553
  have hstable : (prefixWord ++ tailWord_4186553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186553).length < 2 ^ (prefixWord ++ tailWord_4186553).sum := by decide
  have hdescent : baseEnd_4186553 < baseStart_4186553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186593 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_4186593 : Nat := 118140960795 + 4186593 * 2 ^ 59
def prefixEnd_4186593 : Nat := 4983230072969 + 3 ^ 40 * 4186593 * 2
def baseEnd_4186593 : Nat := 2149734513748843669333715

theorem tailTrace_4186593 : CollatzResearch.WordTrace tailWord_4186593 prefixEnd_4186593 2149734513748843669333715 := by
  unfold tailWord_4186593
  simp only [CollatzResearch.WordTrace]
  refine ⟨152697591321696049004404433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101798394214464032669602955 152697591321696049004404433)
  ·
    refine ⟨114523193491272036753303325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152697591321696049004404433 114523193491272036753303325)
    ·
      refine ⟨42946197559227013782488747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114523193491272036753303325 42946197559227013782488747)
      ·
        refine ⟨64419296338840520673733121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42946197559227013782488747 64419296338840520673733121)
        ·
          refine ⟨48314472254130390505299841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64419296338840520673733121 48314472254130390505299841)
          ·
            refine ⟨36235854190597792878974881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48314472254130390505299841 36235854190597792878974881)
            ·
              refine ⟨27176890642948344659231161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36235854190597792878974881 27176890642948344659231161)
              ·
                refine ⟨20382667982211258494423371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27176890642948344659231161 20382667982211258494423371)
                ·
                  refine ⟨30574001973316887741635057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20382667982211258494423371 30574001973316887741635057)
                  ·
                    refine ⟨22930501479987665806226293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30574001973316887741635057 22930501479987665806226293)
                    ·
                      refine ⟨2149734513748843669333715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22930501479987665806226293 2149734513748843669333715)
                      ·
                        rfl

theorem cell23_4186593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_4186593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186593 prefixEnd_4186593 := by exact prefixLift 4186593
  have htrace : WordTrace (prefixWord ++ tailWord_4186593) baseStart_4186593 baseEnd_4186593 := by
    simpa [prefixWord, tailWord_4186593, baseEnd_4186593] using wordTrace_append hprefix tailTrace_4186593
  have hstable : (prefixWord ++ tailWord_4186593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186593).length < 2 ^ (prefixWord ++ tailWord_4186593).sum := by decide
  have hdescent : baseEnd_4186593 < baseStart_4186593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186600 : List Nat := [2, 1, 4, 1, 1, 4, 1, 2, 2, 5]
def baseStart_4186600 : Nat := 118140960795 + 4186600 * 2 ^ 59
def prefixEnd_4186600 : Nat := 4983230072969 + 3 ^ 40 * 4186600 * 2
def baseEnd_4186600 : Nat := 716579369371141713982061

theorem tailTrace_4186600 : CollatzResearch.WordTrace tailWord_4186600 prefixEnd_4186600 716579369371141713982061 := by
  unfold tailWord_4186600
  simp only [CollatzResearch.WordTrace]
  refine ⟨76348923316335344599954627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101798564421780459466606169 76348923316335344599954627)
  ·
    refine ⟨114523384974503016899931941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76348923316335344599954627 114523384974503016899931941)
    ·
      refine ⟨21473134682719315668737239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114523384974503016899931941 21473134682719315668737239)
      ·
        refine ⟨32209702024078973503105859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21473134682719315668737239 32209702024078973503105859)
        ·
          refine ⟨48314553036118460254658789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32209702024078973503105859 48314553036118460254658789)
          ·
            refine ⟨9058978694272211297748523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48314553036118460254658789 9058978694272211297748523)
            ·
              refine ⟨13588468041408316946622785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9058978694272211297748523 13588468041408316946622785)
              ·
                refine ⟨10191351031056237709967089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13588468041408316946622785 10191351031056237709967089)
                ·
                  refine ⟨7643513273292178282475317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10191351031056237709967089 7643513273292178282475317)
                  ·
                    refine ⟨716579369371141713982061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7643513273292178282475317 716579369371141713982061)
                    ·
                      rfl

theorem cell23_4186600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_4186600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186600 prefixEnd_4186600 := by exact prefixLift 4186600
  have htrace : WordTrace (prefixWord ++ tailWord_4186600) baseStart_4186600 baseEnd_4186600 := by
    simpa [prefixWord, tailWord_4186600, baseEnd_4186600] using wordTrace_append hprefix tailTrace_4186600
  have hstable : (prefixWord ++ tailWord_4186600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186600).length < 2 ^ (prefixWord ++ tailWord_4186600).sum := by decide
  have hdescent : baseEnd_4186600 < baseStart_4186600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186620 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 1, 6, 2]
def baseStart_4186620 : Nat := 118140960795 + 4186620 * 2 ^ 59
def prefixEnd_4186620 : Nat := 4983230072969 + 3 ^ 40 * 4186620 * 2
def baseEnd_4186620 : Nat := 2149748377726515063696091

theorem tailTrace_4186620 : CollatzResearch.WordTrace tailWord_4186620 prefixEnd_4186620 2149748377726515063696091 := by
  unfold tailWord_4186620
  simp only [CollatzResearch.WordTrace]
  refine ⟨76349288046299116307818657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101799050728398821743758209 76349288046299116307818657)
  ·
    refine ⟨57261966034724337230863993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76349288046299116307818657 57261966034724337230863993)
    ·
      refine ⟨42946474526043252923147995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57261966034724337230863993 42946474526043252923147995)
      ·
        refine ⟨64419711789064879384721993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42946474526043252923147995 64419711789064879384721993)
        ·
          refine ⟨48314783841798659538541495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64419711789064879384721993 48314783841798659538541495)
          ·
            refine ⟨72472175762697989307812243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48314783841798659538541495 72472175762697989307812243)
            ·
              refine ⟨108708263644046983961718365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72472175762697989307812243 108708263644046983961718365)
              ·
                refine ⟨40765598866517618985644387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108708263644046983961718365 40765598866517618985644387)
                ·
                  refine ⟨61148398299776428478466581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40765598866517618985644387 61148398299776428478466581)
                  ·
                    refine ⟨2866331170302020084928121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61148398299776428478466581 2866331170302020084928121)
                    ·
                      refine ⟨2149748377726515063696091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2866331170302020084928121 2149748377726515063696091)
                      ·
                        rfl

theorem cell23_4186620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_4186620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186620 prefixEnd_4186620 := by exact prefixLift 4186620
  have htrace : WordTrace (prefixWord ++ tailWord_4186620) baseStart_4186620 baseEnd_4186620 := by
    simpa [prefixWord, tailWord_4186620, baseEnd_4186620] using wordTrace_append hprefix tailTrace_4186620
  have hstable : (prefixWord ++ tailWord_4186620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186620).length < 2 ^ (prefixWord ++ tailWord_4186620).sum := by decide
  have hdescent : baseEnd_4186620 < baseStart_4186620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186687 : List Nat := [1, 1, 2, 2, 3, 2, 3, 2, 3, 1, 3]
def baseStart_4186687 : Nat := 118140960795 + 4186687 * 2 ^ 59
def prefixEnd_4186687 : Nat := 4983230072969 + 3 ^ 40 * 4186687 * 2
def baseEnd_4186687 : Nat := 2149782780930366301558283

theorem tailTrace_4186687 : CollatzResearch.WordTrace tailWord_4186687 prefixEnd_4186687 2149782780930366301558283 := by
  unfold tailWord_4186687
  simp only [CollatzResearch.WordTrace]
  refine ⟨152701019783355503058326315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101800679855570335372217543 152701019783355503058326315)
  ·
    refine ⟨229051529675033254587489473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152701019783355503058326315 229051529675033254587489473)
    ·
      refine ⟨171788647256274940940617105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229051529675033254587489473 171788647256274940940617105)
      ·
        refine ⟨128841485442206205705462829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171788647256274940940617105 128841485442206205705462829)
        ·
          refine ⟨48315557040827327139548561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128841485442206205705462829 48315557040827327139548561)
          ·
            refine ⟨36236667780620495354661421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48315557040827327139548561 36236667780620495354661421)
            ·
              refine ⟨13588750417732685757998033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36236667780620495354661421 13588750417732685757998033)
              ·
                refine ⟨10191562813299514318498525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13588750417732685757998033 10191562813299514318498525)
                ·
                  refine ⟨3821836054987317869436947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10191562813299514318498525 3821836054987317869436947)
                  ·
                    refine ⟨5732754082480976804155421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3821836054987317869436947 5732754082480976804155421)
                    ·
                      refine ⟨2149782780930366301558283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5732754082480976804155421 2149782780930366301558283)
                      ·
                        rfl

theorem cell23_4186687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 1, 3].length) (baseStart_4186687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186687 prefixEnd_4186687 := by exact prefixLift 4186687
  have htrace : WordTrace (prefixWord ++ tailWord_4186687) baseStart_4186687 baseEnd_4186687 := by
    simpa [prefixWord, tailWord_4186687, baseEnd_4186687] using wordTrace_append hprefix tailTrace_4186687
  have hstable : (prefixWord ++ tailWord_4186687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186687).length < 2 ^ (prefixWord ++ tailWord_4186687).sum := by decide
  have hdescent : baseEnd_4186687 < baseStart_4186687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186777 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 4, 1, 3]
def baseStart_4186777 : Nat := 118140960795 + 4186777 * 2 ^ 59
def prefixEnd_4186777 : Nat := 4983230072969 + 3 ^ 40 * 4186777 * 2
def baseEnd_4186777 : Nat := 2149828994189270949432869

theorem tailTrace_4186777 : CollatzResearch.WordTrace tailWord_4186777 prefixEnd_4186777 2149828994189270949432869 := by
  unfold tailWord_4186777
  simp only [CollatzResearch.WordTrace]
  refine ⟨152704302353029448429102585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101802868235352965619401723 152704302353029448429102585)
  ·
    refine ⟨114528226764772086321826939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152704302353029448429102585 114528226764772086321826939)
    ·
      refine ⟨171792340147158129482740409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114528226764772086321826939 171792340147158129482740409)
      ·
        refine ⟨128844255110368597112055307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171792340147158129482740409 128844255110368597112055307)
        ·
          refine ⟨193266382665552895668082961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128844255110368597112055307 193266382665552895668082961)
          ·
            refine ⟨144949786999164671751062221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193266382665552895668082961 144949786999164671751062221)
            ·
              refine ⟨54356170124686751906648333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144949786999164671751062221 54356170124686751906648333)
              ·
                refine ⟨20383563796757531964993125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54356170124686751906648333 20383563796757531964993125)
                ·
                  refine ⟨3821918211892037243436211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20383563796757531964993125 3821918211892037243436211)
                  ·
                    refine ⟨5732877317838055865154317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3821918211892037243436211 5732877317838055865154317)
                    ·
                      refine ⟨2149828994189270949432869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5732877317838055865154317 2149828994189270949432869)
                      ·
                        rfl

theorem cell23_4186777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 1, 3].length) (baseStart_4186777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186777 prefixEnd_4186777 := by exact prefixLift 4186777
  have htrace : WordTrace (prefixWord ++ tailWord_4186777) baseStart_4186777 baseEnd_4186777 := by
    simpa [prefixWord, tailWord_4186777, baseEnd_4186777] using wordTrace_append hprefix tailTrace_4186777
  have hstable : (prefixWord ++ tailWord_4186777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186777).length < 2 ^ (prefixWord ++ tailWord_4186777).sum := by decide
  have hdescent : baseEnd_4186777 < baseStart_4186777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186798 : List Nat := [4, 1, 4, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_4186798 : Nat := 118140960795 + 4186798 * 2 ^ 59
def prefixEnd_4186798 : Nat := 4983230072969 + 3 ^ 40 * 4186798 * 2
def baseEnd_4186798 : Nat := 2149839777283015367270273

theorem tailTrace_4186798 : CollatzResearch.WordTrace tailWord_4186798 prefixEnd_4186798 2149839777283015367270273 := by
  unfold tailWord_4186798
  simp only [CollatzResearch.WordTrace]
  refine ⟨19088133535744171126952131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101803378857302246010411365 19088133535744171126952131)
  ·
    refine ⟨28632200303616256690428197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19088133535744171126952131 28632200303616256690428197)
    ·
      refine ⟨5368537556928048129455287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28632200303616256690428197 5368537556928048129455287)
      ·
        refine ⟨8052806335392072194182931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5368537556928048129455287 8052806335392072194182931)
        ·
          refine ⟨12079209503088108291274397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8052806335392072194182931 12079209503088108291274397)
          ·
            refine ⟨4529703563658040609227899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12079209503088108291274397 4529703563658040609227899)
            ·
              refine ⟨6794555345487060913841849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4529703563658040609227899 6794555345487060913841849)
              ·
                refine ⟨5095916509115295685381387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6794555345487060913841849 5095916509115295685381387)
                ·
                  refine ⟨7643874763672943528072081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095916509115295685381387 7643874763672943528072081)
                  ·
                    refine ⟨5732906072754707646054061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7643874763672943528072081 5732906072754707646054061)
                    ·
                      refine ⟨2149839777283015367270273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5732906072754707646054061 2149839777283015367270273)
                      ·
                        rfl

theorem cell23_4186798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_4186798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186798 prefixEnd_4186798 := by exact prefixLift 4186798
  have htrace : WordTrace (prefixWord ++ tailWord_4186798) baseStart_4186798 baseEnd_4186798 := by
    simpa [prefixWord, tailWord_4186798, baseEnd_4186798] using wordTrace_append hprefix tailTrace_4186798
  have hstable : (prefixWord ++ tailWord_4186798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186798).length < 2 ^ (prefixWord ++ tailWord_4186798).sum := by decide
  have hdescent : baseEnd_4186798 < baseStart_4186798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186829 : List Nat := [1, 6, 2, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_4186829 : Nat := 118140960795 + 4186829 * 2 ^ 59
def prefixEnd_4186829 : Nat := 4983230072969 + 3 ^ 40 * 4186829 * 2
def baseEnd_4186829 : Nat := 2149855695183304745982631

theorem tailTrace_4186829 : CollatzResearch.WordTrace tailWord_4186829 prefixEnd_4186829 2149855695183304745982631 := by
  unfold tailWord_4186829
  simp only [CollatzResearch.WordTrace]
  refine ⟨152706198948841061309995541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101804132632560707539997027 152706198948841061309995541)
  ·
    refine ⟨7158103075726924748906041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152706198948841061309995541 7158103075726924748906041)
    ·
      refine ⟨5368577306795193561679531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7158103075726924748906041 5368577306795193561679531)
      ·
        refine ⟨8052865960192790342519297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5368577306795193561679531 8052865960192790342519297)
        ·
          refine ⟨6039649470144592756889473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8052865960192790342519297 6039649470144592756889473)
          ·
            refine ⟨4529737102608444567667105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6039649470144592756889473 4529737102608444567667105)
            ·
              refine ⟨3397302826956333425750329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4529737102608444567667105 3397302826956333425750329)
              ·
                refine ⟨2547977120217250069312747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3397302826956333425750329 2547977120217250069312747)
                ·
                  refine ⟨3821965680325875103969121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2547977120217250069312747 3821965680325875103969121)
                  ·
                    refine ⟨2866474260244406327976841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3821965680325875103969121 2866474260244406327976841)
                    ·
                      refine ⟨2149855695183304745982631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2866474260244406327976841 2149855695183304745982631)
                      ·
                        rfl

theorem cell23_4186829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_4186829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186829 prefixEnd_4186829 := by exact prefixLift 4186829
  have htrace : WordTrace (prefixWord ++ tailWord_4186829) baseStart_4186829 baseEnd_4186829 := by
    simpa [prefixWord, tailWord_4186829, baseEnd_4186829] using wordTrace_append hprefix tailTrace_4186829
  have hstable : (prefixWord ++ tailWord_4186829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186829).length < 2 ^ (prefixWord ++ tailWord_4186829).sum := by decide
  have hdescent : baseEnd_4186829 < baseStart_4186829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186844 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 2, 6]
def baseStart_4186844 : Nat := 118140960795 + 4186844 * 2 ^ 59
def prefixEnd_4186844 : Nat := 4983230072969 + 3 ^ 40 * 4186844 * 2
def baseEnd_4186844 : Nat := 716621132464374062431687

theorem tailTrace_4186844 : CollatzResearch.WordTrace tailWord_4186844 prefixEnd_4186844 716621132464374062431687 := by
  unfold tailWord_4186844
  simp only [CollatzResearch.WordTrace]
  refine ⟨76353373021893359435895793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101804497362524479247861057 76353373021893359435895793)
  ·
    refine ⟨57265029766420019576921845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76353373021893359435895793 57265029766420019576921845)
    ·
      refine ⟨5368596540601876835336423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57265029766420019576921845 5368596540601876835336423)
      ·
        refine ⟨8052894810902815253004635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5368596540601876835336423 8052894810902815253004635)
        ·
          refine ⟨12079342216354222879506953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8052894810902815253004635 12079342216354222879506953)
          ·
            refine ⟨9059506662265667159630215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12079342216354222879506953 9059506662265667159630215)
            ·
              refine ⟨13589259993398500739445323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9059506662265667159630215 13589259993398500739445323)
              ·
                refine ⟨20383889990097751109167985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13589259993398500739445323 20383889990097751109167985)
                ·
                  refine ⟨15287917492573313331875989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20383889990097751109167985 15287917492573313331875989)
                  ·
                    refine ⟨716621132464374062431687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15287917492573313331875989 716621132464374062431687)
                    ·
                      rfl

theorem cell23_4186844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_4186844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186844 prefixEnd_4186844 := by exact prefixLift 4186844
  have htrace : WordTrace (prefixWord ++ tailWord_4186844) baseStart_4186844 baseEnd_4186844 := by
    simpa [prefixWord, tailWord_4186844, baseEnd_4186844] using wordTrace_append hprefix tailTrace_4186844
  have hstable : (prefixWord ++ tailWord_4186844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186844).length < 2 ^ (prefixWord ++ tailWord_4186844).sum := by decide
  have hdescent : baseEnd_4186844 < baseStart_4186844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186847 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 4]
def baseStart_4186847 : Nat := 118140960795 + 4186847 * 2 ^ 59
def prefixEnd_4186847 : Nat := 4983230072969 + 3 ^ 40 * 4186847 * 2
def baseEnd_4186847 : Nat := 2149864937835085675557547

theorem tailTrace_4186847 : CollatzResearch.WordTrace tailWord_4186847 prefixEnd_4186847 2149864937835085675557547 := by
  unfold tailWord_4186847
  simp only [CollatzResearch.WordTrace]
  refine ⟨152706855462775850384150795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101804570308517233589433863 152706855462775850384150795)
  ·
    refine ⟨229060283194163775576226193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152706855462775850384150795 229060283194163775576226193)
    ·
      refine ⟨171795212395622831682169645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229060283194163775576226193 171795212395622831682169645)
      ·
        refine ⟨64423204648358561880813617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171795212395622831682169645 64423204648358561880813617)
        ·
          refine ⟨48317403486268921410610213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64423204648358561880813617 48317403486268921410610213)
          ·
            refine ⟨9059513153675422764489415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48317403486268921410610213 9059513153675422764489415)
            ·
              refine ⟨13589269730513134146734123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9059513153675422764489415 13589269730513134146734123)
              ·
                refine ⟨20383904595769701220101185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13589269730513134146734123 20383904595769701220101185)
                ·
                  refine ⟨15287928446827275915075889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20383904595769701220101185 15287928446827275915075889)
                  ·
                    refine ⟨11465946335120456936306917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15287928446827275915075889 11465946335120456936306917)
                    ·
                      refine ⟨2149864937835085675557547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11465946335120456936306917 2149864937835085675557547)
                      ·
                        rfl

theorem cell23_4186847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_4186847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186847 prefixEnd_4186847 := by exact prefixLift 4186847
  have htrace : WordTrace (prefixWord ++ tailWord_4186847) baseStart_4186847 baseEnd_4186847 := by
    simpa [prefixWord, tailWord_4186847, baseEnd_4186847] using wordTrace_append hprefix tailTrace_4186847
  have hstable : (prefixWord ++ tailWord_4186847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186847).length < 2 ^ (prefixWord ++ tailWord_4186847).sum := by decide
  have hdescent : baseEnd_4186847 < baseStart_4186847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186851 : List Nat := [1, 1, 1, 7, 1, 2, 2, 1, 1, 4, 2]
def baseStart_4186851 : Nat := 118140960795 + 4186851 * 2 ^ 59
def prefixEnd_4186851 : Nat := 4983230072969 + 3 ^ 40 * 4186851 * 2
def baseEnd_4186851 : Nat := 2149866991757703659907529

theorem tailTrace_4186851 : CollatzResearch.WordTrace tailWord_4186851 prefixEnd_4186851 2149866991757703659907529 := by
  unfold tailWord_4186851
  simp only [CollatzResearch.WordTrace]
  refine ⟨152707001354761359067296407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101804667569840906044864271 152707001354761359067296407)
  ·
    refine ⟨229060502032142038600944611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152707001354761359067296407 229060502032142038600944611)
    ·
      refine ⟨343590753048213057901416917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229060502032142038600944611 343590753048213057901416917)
      ·
        refine ⟨8052908274567493544564459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 343590753048213057901416917 8052908274567493544564459)
        ·
          refine ⟨12079362411851240316846689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8052908274567493544564459 12079362411851240316846689)
          ·
            refine ⟨9059521808888430237635017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12079362411851240316846689 9059521808888430237635017)
            ·
              refine ⟨6794641356666322678226263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9059521808888430237635017 6794641356666322678226263)
              ·
                refine ⟨10191962034999484017339395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6794641356666322678226263 10191962034999484017339395)
                ·
                  refine ⟨15287943052499226026009093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10191962034999484017339395 15287943052499226026009093)
                  ·
                    refine ⟨2866489322343604879876705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15287943052499226026009093 2866489322343604879876705)
                    ·
                      refine ⟨2149866991757703659907529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2866489322343604879876705 2149866991757703659907529)
                      ·
                        rfl

theorem cell23_4186851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_4186851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186851 prefixEnd_4186851 := by exact prefixLift 4186851
  have htrace : WordTrace (prefixWord ++ tailWord_4186851) baseStart_4186851 baseEnd_4186851 := by
    simpa [prefixWord, tailWord_4186851, baseEnd_4186851] using wordTrace_append hprefix tailTrace_4186851
  have hstable : (prefixWord ++ tailWord_4186851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186851).length < 2 ^ (prefixWord ++ tailWord_4186851).sum := by decide
  have hdescent : baseEnd_4186851 < baseStart_4186851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186925 : List Nat := [1, 5, 3, 2, 1, 2, 1, 3, 5]
def baseStart_4186925 : Nat := 118140960795 + 4186925 * 2 ^ 59
def prefixEnd_4186925 : Nat := 4983230072969 + 3 ^ 40 * 4186925 * 2
def baseEnd_4186925 : Nat := 238878332147348485598021

theorem tailTrace_4186925 : CollatzResearch.WordTrace tailWord_4186925 prefixEnd_4186925 238878332147348485598021 := by
  unfold tailWord_4186925
  simp only [CollatzResearch.WordTrace]
  refine ⟨152709700356493269705490229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101806466904328846470326819 152709700356493269705490229)
  ·
    refine ⟨14316534408421244034889709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152709700356493269705490229 14316534408421244034889709)
    ·
      refine ⟨5368700403157966513083641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14316534408421244034889709 5368700403157966513083641)
      ·
        refine ⟨4026525302368474884812731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5368700403157966513083641 4026525302368474884812731)
        ·
          refine ⟨6039787953552712327219097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4026525302368474884812731 6039787953552712327219097)
          ·
            refine ⟨4529840965164534245414323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6039787953552712327219097 4529840965164534245414323)
            ·
              refine ⟨6794761447746801368121485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4529840965164534245414323 6794761447746801368121485)
              ·
                refine ⟨2548035542905050513045557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6794761447746801368121485 2548035542905050513045557)
                ·
                  refine ⟨238878332147348485598021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2548035542905050513045557 238878332147348485598021)
                  ·
                    rfl

theorem cell23_4186925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_4186925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186925 prefixEnd_4186925 := by exact prefixLift 4186925
  have htrace : WordTrace (prefixWord ++ tailWord_4186925) baseStart_4186925 baseEnd_4186925 := by
    simpa [prefixWord, tailWord_4186925, baseEnd_4186925] using wordTrace_append hprefix tailTrace_4186925
  have hstable : (prefixWord ++ tailWord_4186925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186925).length < 2 ^ (prefixWord ++ tailWord_4186925).sum := by decide
  have hdescent : baseEnd_4186925 < baseStart_4186925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186941 : List Nat := [1, 4, 1, 4, 2, 1, 1, 2, 2, 1, 4]
def baseStart_4186941 : Nat := 118140960795 + 4186941 * 2 ^ 59
def prefixEnd_4186941 : Nat := 4983230072969 + 3 ^ 40 * 4186941 * 2
def baseEnd_4186941 : Nat := 2149913205016608307782115

theorem tailTrace_4186941 : CollatzResearch.WordTrace tailWord_4186941 prefixEnd_4186941 2149913205016608307782115 := by
  unfold tailWord_4186941
  simp only [CollatzResearch.WordTrace]
  refine ⟨152710283924435304438072677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101806855949623536292048451 152710283924435304438072677)
  ·
    refine ⟨28633178235831619582138627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152710283924435304438072677 28633178235831619582138627)
    ·
      refine ⟨42949767353747429373207941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28633178235831619582138627 42949767353747429373207941)
      ·
        refine ⟨8053081378827643007476489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42949767353747429373207941 8053081378827643007476489)
        ·
          refine ⟨6039811034120732255607367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8053081378827643007476489 6039811034120732255607367)
          ·
            refine ⟨9059716551181098383411051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6039811034120732255607367 9059716551181098383411051)
            ·
              refine ⟨13589574826771647575116577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9059716551181098383411051 13589574826771647575116577)
              ·
                refine ⟨10192181120078735681337433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13589574826771647575116577 10192181120078735681337433)
                ·
                  refine ⟨7644135840059051761003075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10192181120078735681337433 7644135840059051761003075)
                  ·
                    refine ⟨11466203760088577641504613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7644135840059051761003075 11466203760088577641504613)
                    ·
                      refine ⟨2149913205016608307782115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11466203760088577641504613 2149913205016608307782115)
                      ·
                        rfl

theorem cell23_4186941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_4186941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186941 prefixEnd_4186941 := by exact prefixLift 4186941
  have htrace : WordTrace (prefixWord ++ tailWord_4186941) baseStart_4186941 baseEnd_4186941 := by
    simpa [prefixWord, tailWord_4186941, baseEnd_4186941] using wordTrace_append hprefix tailTrace_4186941
  have hstable : (prefixWord ++ tailWord_4186941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186941).length < 2 ^ (prefixWord ++ tailWord_4186941).sum := by decide
  have hdescent : baseEnd_4186941 < baseStart_4186941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186947 : List Nat := [1, 1, 1, 3, 1, 4, 2, 4, 6]
def baseStart_4186947 : Nat := 118140960795 + 4186947 * 2 ^ 59
def prefixEnd_4186947 : Nat := 4983230072969 + 3 ^ 40 * 4186947 * 2
def baseEnd_4186947 : Nat := 238879587322281698256343

theorem tailTrace_4186947 : CollatzResearch.WordTrace tailWord_4186947 prefixEnd_4186947 238879587322281698256343 := by
  unfold tailWord_4186947
  simp only [CollatzResearch.WordTrace]
  refine ⟨152710502762413567462791095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101807001841609044975194063 152710502762413567462791095)
  ·
    refine ⟨229065754143620351194186643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152710502762413567462791095 229065754143620351194186643)
    ·
      refine ⟨343598631215430526791279965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229065754143620351194186643 343598631215430526791279965)
      ·
        refine ⟨128849486705786447546729987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343598631215430526791279965 128849486705786447546729987)
        ·
          refine ⟨193274230058679671320094981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128849486705786447546729987 193274230058679671320094981)
          ·
            refine ⟨36238918136002438372517809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193274230058679671320094981 36238918136002438372517809)
            ·
              refine ⟨27179188602001828779388357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36238918136002438372517809 27179188602001828779388357)
              ·
                refine ⟨5096097862875342896135317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27179188602001828779388357 5096097862875342896135317)
                ·
                  refine ⟨238879587322281698256343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5096097862875342896135317 238879587322281698256343)
                  ·
                    rfl

theorem cell23_4186947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 6].length) (baseStart_4186947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186947 prefixEnd_4186947 := by exact prefixLift 4186947
  have htrace : WordTrace (prefixWord ++ tailWord_4186947) baseStart_4186947 baseEnd_4186947 := by
    simpa [prefixWord, tailWord_4186947, baseEnd_4186947] using wordTrace_append hprefix tailTrace_4186947
  have hstable : (prefixWord ++ tailWord_4186947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186947).length < 2 ^ (prefixWord ++ tailWord_4186947).sum := by decide
  have hdescent : baseEnd_4186947 < baseStart_4186947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186978 : List Nat := [3, 3, 2, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_4186978 : Nat := 118140960795 + 4186978 * 2 ^ 59
def prefixEnd_4186978 : Nat := 4983230072969 + 3 ^ 40 * 4186978 * 2
def baseEnd_4186978 : Nat := 2149932203800824663019445

theorem tailTrace_4186978 : CollatzResearch.WordTrace tailWord_4186978 prefixEnd_4186978 2149932203800824663019445 := by
  unfold tailWord_4186978
  simp only [CollatzResearch.WordTrace]
  refine ⟨38177908356325314939292397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101807755616867506504779725 38177908356325314939292397)
  ·
    refine ⟨14316715633621993102234649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38177908356325314939292397 14316715633621993102234649)
    ·
      refine ⟨10737536725216494826675987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14316715633621993102234649 10737536725216494826675987)
      ·
        refine ⟨16106305087824742240013981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10737536725216494826675987 16106305087824742240013981)
        ·
          refine ⟨6039864407934278340005243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16106305087824742240013981 6039864407934278340005243)
          ·
            refine ⟨9059796611901417510007865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6039864407934278340005243 9059796611901417510007865)
            ·
              refine ⟨6794847458926063132505899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9059796611901417510007865 6794847458926063132505899)
              ·
                refine ⟨10192271188389094698758849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6794847458926063132505899 10192271188389094698758849)
                ·
                  refine ⟨7644203391291821024069137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10192271188389094698758849 7644203391291821024069137)
                  ·
                    refine ⟨5733152543468865768051853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7644203391291821024069137 5733152543468865768051853)
                    ·
                      refine ⟨2149932203800824663019445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5733152543468865768051853 2149932203800824663019445)
                      ·
                        rfl

theorem cell23_4186978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_4186978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186978 prefixEnd_4186978 := by exact prefixLift 4186978
  have htrace : WordTrace (prefixWord ++ tailWord_4186978) baseStart_4186978 baseEnd_4186978 := by
    simpa [prefixWord, tailWord_4186978, baseEnd_4186978] using wordTrace_append hprefix tailTrace_4186978
  have hstable : (prefixWord ++ tailWord_4186978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186978).length < 2 ^ (prefixWord ++ tailWord_4186978).sum := by decide
  have hdescent : baseEnd_4186978 < baseStart_4186978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186994 : List Nat := [3, 2, 1, 2, 1, 1, 2, 5, 1, 5]
def baseStart_4186994 : Nat := 118140960795 + 4186994 * 2 ^ 59
def prefixEnd_4186994 : Nat := 4983230072969 + 3 ^ 40 * 4186994 * 2
def baseEnd_4186994 : Nat := 716646806497098866806457

theorem tailTrace_4186994 : CollatzResearch.WordTrace tailWord_4186994 prefixEnd_4186994 716646806497098866806457 := by
  unfold tailWord_4186994
  simp only [CollatzResearch.WordTrace]
  refine ⟨38178054248310823622438009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101808144662162196326501357 38178054248310823622438009)
  ·
    refine ⟨28633540686233117716828507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38178054248310823622438009 28633540686233117716828507)
    ·
      refine ⟨42950311029349676575242761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28633540686233117716828507 42950311029349676575242761)
      ·
        refine ⟨32212733272012257431432071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42950311029349676575242761 32212733272012257431432071)
        ·
          refine ⟨48319099908018386147148107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32212733272012257431432071 48319099908018386147148107)
          ·
            refine ⟨72478649862027579220722161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48319099908018386147148107 72478649862027579220722161)
            ·
              refine ⟨54358987396520684415541621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72478649862027579220722161 54358987396520684415541621)
              ·
                refine ⟨5096155068423814163957027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54358987396520684415541621 5096155068423814163957027)
                ·
                  refine ⟨7644232602635721245935541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5096155068423814163957027 7644232602635721245935541)
                  ·
                    refine ⟨716646806497098866806457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7644232602635721245935541 716646806497098866806457)
                    ·
                      rfl

theorem cell23_4186994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_4186994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4186994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4186994 prefixEnd_4186994 := by exact prefixLift 4186994
  have htrace : WordTrace (prefixWord ++ tailWord_4186994) baseStart_4186994 baseEnd_4186994 := by
    simpa [prefixWord, tailWord_4186994, baseEnd_4186994] using wordTrace_append hprefix tailTrace_4186994
  have hstable : (prefixWord ++ tailWord_4186994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186994).length < 2 ^ (prefixWord ++ tailWord_4186994).sum := by decide
  have hdescent : baseEnd_4186994 < baseStart_4186994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187001 : List Nat := [1, 2, 1, 3, 2, 3, 2, 2, 2, 3, 2]
def baseStart_4187001 : Nat := 118140960795 + 4187001 * 2 ^ 59
def prefixEnd_4187001 : Nat := 4983230072969 + 3 ^ 40 * 4187001 * 2
def baseEnd_4187001 : Nat := 2149944013855878073031839

theorem tailTrace_4187001 : CollatzResearch.WordTrace tailWord_4187001 prefixEnd_4187001 2149944013855878073031839 := by
  unfold tailWord_4187001
  simp only [CollatzResearch.WordTrace]
  refine ⟨152712472304217934685256857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101808314869478623123504571 152712472304217934685256857)
  ·
    refine ⟨114534354228163451013942643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152712472304217934685256857 114534354228163451013942643)
    ·
      refine ⟨171801531342245176520913965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114534354228163451013942643 171801531342245176520913965)
      ·
        refine ⟨64425574253341941195342737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171801531342245176520913965 64425574253341941195342737)
        ·
          refine ⟨48319180690006455896507053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64425574253341941195342737 48319180690006455896507053)
          ·
            refine ⟨18119692758752420961190145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48319180690006455896507053 18119692758752420961190145)
            ·
              refine ⟨13589769569064315720892609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18119692758752420961190145 13589769569064315720892609)
              ·
                refine ⟨10192327176798236790669457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13589769569064315720892609 10192327176798236790669457)
                ·
                  refine ⟨7644245382598677593002093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10192327176798236790669457 7644245382598677593002093)
                  ·
                    refine ⟨2866592018474504097375785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7644245382598677593002093 2866592018474504097375785)
                    ·
                      refine ⟨2149944013855878073031839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2866592018474504097375785 2149944013855878073031839)
                      ·
                        rfl

theorem cell23_4187001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_4187001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187001 prefixEnd_4187001 := by exact prefixLift 4187001
  have htrace : WordTrace (prefixWord ++ tailWord_4187001) baseStart_4187001 baseEnd_4187001 := by
    simpa [prefixWord, tailWord_4187001, baseEnd_4187001] using wordTrace_append hprefix tailTrace_4187001
  have hstable : (prefixWord ++ tailWord_4187001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187001).length < 2 ^ (prefixWord ++ tailWord_4187001).sum := by decide
  have hdescent : baseEnd_4187001 < baseStart_4187001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187044 : List Nat := [2, 3, 1, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_4187044 : Nat := 118140960795 + 4187044 * 2 ^ 59
def prefixEnd_4187044 : Nat := 4983230072969 + 3 ^ 40 * 4187044 * 2
def baseEnd_4187044 : Nat := 2149966093524021404794141

theorem tailTrace_4187044 : CollatzResearch.WordTrace tailWord_4187044 prefixEnd_4187044 2149966093524021404794141 := by
  unfold tailWord_4187044
  simp only [CollatzResearch.WordTrace]
  refine ⟨76357020321531076514536093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101809360428708102019381457 76357020321531076514536093)
  ·
    refine ⟨28633882620574153692951035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76357020321531076514536093 28633882620574153692951035)
    ·
      refine ⟨42950823930861230539426553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28633882620574153692951035 42950823930861230539426553)
      ·
        refine ⟨32213117948145922904569915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42950823930861230539426553 32213117948145922904569915)
        ·
          refine ⟨48319676922218884356854873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32213117948145922904569915 48319676922218884356854873)
          ·
            refine ⟨36239757691664163267641155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48319676922218884356854873 36239757691664163267641155)
            ·
              refine ⟨54359636537496244901461733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36239757691664163267641155 54359636537496244901461733)
              ·
                refine ⟨10192431850780545919024075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54359636537496244901461733 10192431850780545919024075)
                ·
                  refine ⟨15288647776170818878536113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10192431850780545919024075 15288647776170818878536113)
                  ·
                    refine ⟨11466485832128114158902085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15288647776170818878536113 11466485832128114158902085)
                    ·
                      refine ⟨2149966093524021404794141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11466485832128114158902085 2149966093524021404794141)
                      ·
                        rfl

theorem cell23_4187044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_4187044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187044 prefixEnd_4187044 := by exact prefixLift 4187044
  have htrace : WordTrace (prefixWord ++ tailWord_4187044) baseStart_4187044 baseEnd_4187044 := by
    simpa [prefixWord, tailWord_4187044, baseEnd_4187044] using wordTrace_append hprefix tailTrace_4187044
  have hstable : (prefixWord ++ tailWord_4187044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187044).length < 2 ^ (prefixWord ++ tailWord_4187044).sum := by decide
  have hdescent : baseEnd_4187044 < baseStart_4187044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187065 : List Nat := [1, 2, 1, 4, 2, 2, 2, 4, 1, 2, 2]
def baseStart_4187065 : Nat := 118140960795 + 4187065 * 2 ^ 59
def prefixEnd_4187065 : Nat := 4983230072969 + 3 ^ 40 * 4187065 * 2
def baseEnd_4187065 : Nat := 2149976876617765822631545

theorem tailTrace_4187065 : CollatzResearch.WordTrace tailWord_4187065 prefixEnd_4187065 2149976876617765822631545 := by
  unfold tailWord_4187065
  simp only [CollatzResearch.WordTrace]
  refine ⟨152714806575986073615586649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101809871050657382410391099 152714806575986073615586649)
  ·
    refine ⟨114536104931989555211689987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152714806575986073615586649 114536104931989555211689987)
    ·
      refine ⟨171804157397984332817534981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114536104931989555211689987 171804157397984332817534981)
      ·
        refine ⟨32213279512122062403287809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171804157397984332817534981 32213279512122062403287809)
        ·
          refine ⟨24159959634091546802465857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32213279512122062403287809 24159959634091546802465857)
          ·
            refine ⟨18119969725568660101849393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24159959634091546802465857 18119969725568660101849393)
            ·
              refine ⟨13589977294176495076387045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18119969725568660101849393 13589977294176495076387045)
              ·
                refine ⟨2548120742658092826822571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13589977294176495076387045 2548120742658092826822571)
                ·
                  refine ⟨3822181113987139240233857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2548120742658092826822571 3822181113987139240233857)
                  ·
                    refine ⟨2866635835490354430175393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3822181113987139240233857 2866635835490354430175393)
                    ·
                      refine ⟨2149976876617765822631545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2866635835490354430175393 2149976876617765822631545)
                      ·
                        rfl

theorem cell23_4187065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_4187065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187065 prefixEnd_4187065 := by exact prefixLift 4187065
  have htrace : WordTrace (prefixWord ++ tailWord_4187065) baseStart_4187065 baseEnd_4187065 := by
    simpa [prefixWord, tailWord_4187065, baseEnd_4187065] using wordTrace_append hprefix tailTrace_4187065
  have hstable : (prefixWord ++ tailWord_4187065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187065).length < 2 ^ (prefixWord ++ tailWord_4187065).sum := by decide
  have hdescent : baseEnd_4187065 < baseStart_4187065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187172 : List Nat := [2, 3, 1, 4, 1, 2, 2, 2, 2, 2, 2]
def baseStart_4187172 : Nat := 118140960795 + 4187172 * 2 ^ 59
def prefixEnd_4187172 : Nat := 4983230072969 + 3 ^ 40 * 4187172 * 2
def baseEnd_4187172 : Nat := 2150031819047796903993553

theorem tailTrace_4187172 : CollatzResearch.WordTrace tailWord_4187172 prefixEnd_4187172 2150031819047796903993553 := by
  unfold tailWord_4187172
  simp only [CollatzResearch.WordTrace]
  refine ⟨76359354593299215444865885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101812472791065620593154513 76359354593299215444865885)
  ·
    refine ⟨28634757972487205791824707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76359354593299215444865885 28634757972487205791824707)
    ·
      refine ⟨42952136958730808687737061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28634757972487205791824707 42952136958730808687737061)
      ·
        refine ⟨8053525679762026628950699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42952136958730808687737061 8053525679762026628950699)
        ·
          refine ⟨12080288519643039943426049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8053525679762026628950699 12080288519643039943426049)
          ·
            refine ⟨9060216389732279957569537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12080288519643039943426049 9060216389732279957569537)
            ·
              refine ⟨6795162292299209968177153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9060216389732279957569537 6795162292299209968177153)
              ·
                refine ⟨5096371719224407476132865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6795162292299209968177153 5096371719224407476132865)
                ·
                  refine ⟨3822278789418305607099649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5096371719224407476132865 3822278789418305607099649)
                  ·
                    refine ⟨2866709092063729205324737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3822278789418305607099649 2866709092063729205324737)
                    ·
                      refine ⟨2150031819047796903993553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2866709092063729205324737 2150031819047796903993553)
                      ·
                        rfl

theorem cell23_4187172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_4187172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187172 prefixEnd_4187172 := by exact prefixLift 4187172
  have htrace : WordTrace (prefixWord ++ tailWord_4187172) baseStart_4187172 baseEnd_4187172 := by
    simpa [prefixWord, tailWord_4187172, baseEnd_4187172] using wordTrace_append hprefix tailTrace_4187172
  have hstable : (prefixWord ++ tailWord_4187172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187172).length < 2 ^ (prefixWord ++ tailWord_4187172).sum := by decide
  have hdescent : baseEnd_4187172 < baseStart_4187172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187184 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 5]
def baseStart_4187184 : Nat := 118140960795 + 4187184 * 2 ^ 59
def prefixEnd_4187184 : Nat := 4983230072969 + 3 ^ 40 * 4187184 * 2
def baseEnd_4187184 : Nat := 2150037980815650857043497

theorem tailTrace_4187184 : CollatzResearch.WordTrace tailWord_4187184 prefixEnd_4187184 2150037980815650857043497 := by
  unfold tailWord_4187184
  simp only [CollatzResearch.WordTrace]
  refine ⟨76359573431277478469584303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101812764575036637959445737 76359573431277478469584303)
  ·
    refine ⟨114539360146916217704376455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76359573431277478469584303 114539360146916217704376455)
    ·
      refine ⟨171809040220374326556564683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114539360146916217704376455 171809040220374326556564683)
      ·
        refine ⟨257713560330561489834847025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171809040220374326556564683 257713560330561489834847025)
        ·
          refine ⟨193285170247921117376135269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257713560330561489834847025 193285170247921117376135269)
          ·
            refine ⟨36240969421485209508025363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193285170247921117376135269 36240969421485209508025363)
            ·
              refine ⟨54361454132227814262038045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36240969421485209508025363 54361454132227814262038045)
              ·
                refine ⟨20385545299585430348264267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54361454132227814262038045 20385545299585430348264267)
                ·
                  refine ⟨30578317949378145522396401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20385545299585430348264267 30578317949378145522396401)
                  ·
                    refine ⟨22933738462033609141797301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30578317949378145522396401 22933738462033609141797301)
                    ·
                      refine ⟨2150037980815650857043497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22933738462033609141797301 2150037980815650857043497)
                      ·
                        rfl

theorem cell23_4187184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_4187184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187184 prefixEnd_4187184 := by exact prefixLift 4187184
  have htrace : WordTrace (prefixWord ++ tailWord_4187184) baseStart_4187184 baseEnd_4187184 := by
    simpa [prefixWord, tailWord_4187184, baseEnd_4187184] using wordTrace_append hprefix tailTrace_4187184
  have hstable : (prefixWord ++ tailWord_4187184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187184).length < 2 ^ (prefixWord ++ tailWord_4187184).sum := by decide
  have hdescent : baseEnd_4187184 < baseStart_4187184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187188 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_4187188 : Nat := 118140960795 + 4187188 * 2 ^ 59
def prefixEnd_4187188 : Nat := 4983230072969 + 3 ^ 40 * 4187188 * 2
def baseEnd_4187188 : Nat := 2150040034738268841393479

theorem tailTrace_4187188 : CollatzResearch.WordTrace tailWord_4187188 prefixEnd_4187188 2150040034738268841393479 := by
  unfold tailWord_4187188
  simp only [CollatzResearch.WordTrace]
  refine ⟨76359646377270232811157109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101812861836360310414876145 76359646377270232811157109)
  ·
    refine ⟨7158716847869084326045979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76359646377270232811157109 7158716847869084326045979)
    ·
      refine ⟨10738075271803626489068969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7158716847869084326045979 10738075271803626489068969)
      ·
        refine ⟨8053556453852719866801727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10738075271803626489068969 8053556453852719866801727)
        ·
          refine ⟨12080334680779079800202591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8053556453852719866801727 12080334680779079800202591)
          ·
            refine ⟨18120502021168619700303887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12080334680779079800202591 18120502021168619700303887)
            ·
              refine ⟨27180753031752929550455831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18120502021168619700303887 27180753031752929550455831)
              ·
                refine ⟨40771129547629394325683747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27180753031752929550455831 40771129547629394325683747)
                ·
                  refine ⟨61156694321444091488525621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40771129547629394325683747 61156694321444091488525621)
                  ·
                    refine ⟨5733440092635383577049277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61156694321444091488525621 5733440092635383577049277)
                    ·
                      refine ⟨2150040034738268841393479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5733440092635383577049277 2150040034738268841393479)
                      ·
                        rfl

theorem cell23_4187188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_4187188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187188 prefixEnd_4187188 := by exact prefixLift 4187188
  have htrace : WordTrace (prefixWord ++ tailWord_4187188) baseStart_4187188 baseEnd_4187188 := by
    simpa [prefixWord, tailWord_4187188, baseEnd_4187188] using wordTrace_append hprefix tailTrace_4187188
  have hstable : (prefixWord ++ tailWord_4187188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187188).length < 2 ^ (prefixWord ++ tailWord_4187188).sum := by decide
  have hdescent : baseEnd_4187188 < baseStart_4187188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187211 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 6, 4, 2]
def baseStart_4187211 : Nat := 118140960795 + 4187211 * 2 ^ 59
def prefixEnd_4187211 : Nat := 4983230072969 + 3 ^ 40 * 4187211 * 2
def baseEnd_4187211 : Nat := 2150051844793322251405873

theorem tailTrace_4187211 : CollatzResearch.WordTrace tailWord_4187211 prefixEnd_4187211 2150051844793322251405873 := by
  unfold tailWord_4187211
  simp only [CollatzResearch.WordTrace]
  refine ⟨152720131633457140550401487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101813421088971427033600991 152720131633457140550401487)
  ·
    refine ⟨229080197450185710825602231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152720131633457140550401487 229080197450185710825602231)
    ·
      refine ⟨343620296175278566238403347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229080197450185710825602231 343620296175278566238403347)
      ·
        refine ⟨515430444262917849357605021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343620296175278566238403347 515430444262917849357605021)
        ·
          refine ⟨193286416598594193509101883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515430444262917849357605021 193286416598594193509101883)
          ·
            refine ⟨289929624897891290263652825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193286416598594193509101883 289929624897891290263652825)
            ·
              refine ⟨217447218673418467697739619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289929624897891290263652825 217447218673418467697739619)
              ·
                refine ⟨326170828010127701546609429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217447218673418467697739619 326170828010127701546609429)
                ·
                  refine ⟨15289257562974736009997317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 326170828010127701546609429 15289257562974736009997317)
                  ·
                    refine ⟨2866735793057763001874497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15289257562974736009997317 2866735793057763001874497)
                    ·
                      refine ⟨2150051844793322251405873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2866735793057763001874497 2150051844793322251405873)
                      ·
                        rfl

theorem cell23_4187211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 4, 2].length) (baseStart_4187211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187211 prefixEnd_4187211 := by exact prefixLift 4187211
  have htrace : WordTrace (prefixWord ++ tailWord_4187211) baseStart_4187211 baseEnd_4187211 := by
    simpa [prefixWord, tailWord_4187211, baseEnd_4187211] using wordTrace_append hprefix tailTrace_4187211
  have hstable : (prefixWord ++ tailWord_4187211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187211).length < 2 ^ (prefixWord ++ tailWord_4187211).sum := by decide
  have hdescent : baseEnd_4187211 < baseStart_4187211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187221 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 5, 4]
def baseStart_4187221 : Nat := 118140960795 + 4187221 * 2 ^ 59
def prefixEnd_4187221 : Nat := 4983230072969 + 3 ^ 40 * 4187221 * 2
def baseEnd_4187221 : Nat := 716685659866622404093609

theorem tailTrace_4187221 : CollatzResearch.WordTrace tailWord_4187221 prefixEnd_4187221 716685659866622404093609 := by
  unfold tailWord_4187221
  simp only [CollatzResearch.WordTrace]
  refine ⟨152720496363420912258265517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101813664242280608172177011 152720496363420912258265517)
  ·
    refine ⟨57270186136282842096849569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152720496363420912258265517 57270186136282842096849569)
    ·
      refine ⟨42952639602212131572637177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57270186136282842096849569 42952639602212131572637177)
      ·
        refine ⟨32214479701659098679477883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42952639602212131572637177 32214479701659098679477883)
        ·
          refine ⟨48321719552488648019216825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32214479701659098679477883 48321719552488648019216825)
          ·
            refine ⟨36241289664366486014412619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48321719552488648019216825 36241289664366486014412619)
            ·
              refine ⟨54361934496549729021618929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36241289664366486014412619 54361934496549729021618929)
              ·
                refine ⟨40771450872412296766214197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54361934496549729021618929 40771450872412296766214197)
                ·
                  refine ⟨3822323519288652821832581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40771450872412296766214197 3822323519288652821832581)
                  ·
                    refine ⟨716685659866622404093609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3822323519288652821832581 716685659866622404093609)
                    ·
                      rfl

theorem cell23_4187221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_4187221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187221 prefixEnd_4187221 := by exact prefixLift 4187221
  have htrace : WordTrace (prefixWord ++ tailWord_4187221) baseStart_4187221 baseEnd_4187221 := by
    simpa [prefixWord, tailWord_4187221, baseEnd_4187221] using wordTrace_append hprefix tailTrace_4187221
  have hstable : (prefixWord ++ tailWord_4187221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187221).length < 2 ^ (prefixWord ++ tailWord_4187221).sum := by decide
  have hdescent : baseEnd_4187221 < baseStart_4187221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187224 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 1, 3, 6]
def baseStart_4187224 : Nat := 118140960795 + 4187224 * 2 ^ 59
def prefixEnd_4187224 : Nat := 4983230072969 + 3 ^ 40 * 4187224 * 2
def baseEnd_4187224 : Nat := 2150058520041830700543313

theorem tailTrace_4187224 : CollatzResearch.WordTrace tailWord_4187224 prefixEnd_4187224 2150058520041830700543313 := by
  unfold tailWord_4187224
  simp only [CollatzResearch.WordTrace]
  refine ⟨76360302891205021885312363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101813737188273362513749817 76360302891205021885312363)
  ·
    refine ⟨114540454336807532827968545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76360302891205021885312363 114540454336807532827968545)
    ·
      refine ⟨85905340752605649620976409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114540454336807532827968545 85905340752605649620976409)
      ·
        refine ⟨64429005564454237215732307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85905340752605649620976409 64429005564454237215732307)
        ·
          refine ⟨96643508346681355823598461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64429005564454237215732307 96643508346681355823598461)
          ·
            refine ⟨36241315630005508433849423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96643508346681355823598461 36241315630005508433849423)
            ·
              refine ⟨54361973445008262650774135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36241315630005508433849423 54361973445008262650774135)
              ·
                refine ⟨81542960167512393976161203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54361973445008262650774135 81542960167512393976161203)
                ·
                  refine ⟨122314440251268590964241805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81542960167512393976161203 122314440251268590964241805)
                  ·
                    refine ⟨45867915094225721611590677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122314440251268590964241805 45867915094225721611590677)
                    ·
                      refine ⟨2150058520041830700543313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45867915094225721611590677 2150058520041830700543313)
                      ·
                        rfl

theorem cell23_4187224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_4187224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187224 prefixEnd_4187224 := by exact prefixLift 4187224
  have htrace : WordTrace (prefixWord ++ tailWord_4187224) baseStart_4187224 baseEnd_4187224 := by
    simpa [prefixWord, tailWord_4187224, baseEnd_4187224] using wordTrace_append hprefix tailTrace_4187224
  have hstable : (prefixWord ++ tailWord_4187224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187224).length < 2 ^ (prefixWord ++ tailWord_4187224).sum := by decide
  have hdescent : baseEnd_4187224 < baseStart_4187224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187228 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_4187228 : Nat := 118140960795 + 4187228 * 2 ^ 59
def prefixEnd_4187228 : Nat := 4983230072969 + 3 ^ 40 * 4187228 * 2
def baseEnd_4187228 : Nat := 2150060573964448684893295

theorem tailTrace_4187228 : CollatzResearch.WordTrace tailWord_4187228 prefixEnd_4187228 2150060573964448684893295 := by
  unfold tailWord_4187228
  simp only [CollatzResearch.WordTrace]
  refine ⟨76360375837197776226885169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101813834449597034969180225 76360375837197776226885169)
  ·
    refine ⟨57270281877898332170163877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76360375837197776226885169 57270281877898332170163877)
    ·
      refine ⟨10738177852105937281905727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57270281877898332170163877 10738177852105937281905727)
      ·
        refine ⟨16107266778158905922858591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10738177852105937281905727 16107266778158905922858591)
        ·
          refine ⟨24160900167238358884287887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16107266778158905922858591 24160900167238358884287887)
          ·
            refine ⟨36241350250857538326431831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24160900167238358884287887 36241350250857538326431831)
            ·
              refine ⟨54362025376286307489647747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36241350250857538326431831 54362025376286307489647747)
              ·
                refine ⟨81543038064429461234471621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54362025376286307489647747 81543038064429461234471621)
                ·
                  refine ⟨15289319637080523981463429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81543038064429461234471621 15289319637080523981463429)
                  ·
                    refine ⟨2866747431952598246524393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15289319637080523981463429 2866747431952598246524393)
                    ·
                      refine ⟨2150060573964448684893295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2866747431952598246524393 2150060573964448684893295)
                      ·
                        rfl

theorem cell23_4187228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_4187228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187228 prefixEnd_4187228 := by exact prefixLift 4187228
  have htrace : WordTrace (prefixWord ++ tailWord_4187228) baseStart_4187228 baseEnd_4187228 := by
    simpa [prefixWord, tailWord_4187228, baseEnd_4187228] using wordTrace_append hprefix tailTrace_4187228
  have hstable : (prefixWord ++ tailWord_4187228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187228).length < 2 ^ (prefixWord ++ tailWord_4187228).sum := by decide
  have hdescent : baseEnd_4187228 < baseStart_4187228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187231 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 3]
def baseStart_4187231 : Nat := 118140960795 + 4187231 * 2 ^ 59
def prefixEnd_4187231 : Nat := 4983230072969 + 3 ^ 40 * 4187231 * 2
def baseEnd_4187231 : Nat := 2150062114406412173155781

theorem tailTrace_4187231 : CollatzResearch.WordTrace tailWord_4187231 prefixEnd_4187231 2150062114406412173155781 := by
  unfold tailWord_4187231
  simp only [CollatzResearch.WordTrace]
  refine ⟨152720861093384683966129547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101813907395589789310753031 152720861093384683966129547)
  ·
    refine ⟨229081291640077025949194321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152720861093384683966129547 229081291640077025949194321)
    ·
      refine ⟨171810968730057769461895741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229081291640077025949194321 171810968730057769461895741)
      ·
        refine ⟨64429113273771663548210903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171810968730057769461895741 64429113273771663548210903)
        ·
          refine ⟨96643669910657495322316355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64429113273771663548210903 96643669910657495322316355)
          ·
            refine ⟨144965504865986242983474533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96643669910657495322316355 144965504865986242983474533)
            ·
              refine ⟨27181032162372420559401475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144965504865986242983474533 27181032162372420559401475)
              ·
                refine ⟨40771548243558630839102213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27181032162372420559401475 40771548243558630839102213)
                ·
                  refine ⟨7644665295667243282331665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40771548243558630839102213 7644665295667243282331665)
                  ·
                    refine ⟨5733498971750432461748749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7644665295667243282331665 5733498971750432461748749)
                    ·
                      refine ⟨2150062114406412173155781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5733498971750432461748749 2150062114406412173155781)
                      ·
                        rfl

theorem cell23_4187231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_4187231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187231 prefixEnd_4187231 := by exact prefixLift 4187231
  have htrace : WordTrace (prefixWord ++ tailWord_4187231) baseStart_4187231 baseEnd_4187231 := by
    simpa [prefixWord, tailWord_4187231, baseEnd_4187231] using wordTrace_append hprefix tailTrace_4187231
  have hstable : (prefixWord ++ tailWord_4187231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187231).length < 2 ^ (prefixWord ++ tailWord_4187231).sum := by decide
  have hdescent : baseEnd_4187231 < baseStart_4187231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187261 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 2, 5, 3]
def baseStart_4187261 : Nat := 118140960795 + 4187261 * 2 ^ 59
def prefixEnd_4187261 : Nat := 4983230072969 + 3 ^ 40 * 4187261 * 2
def baseEnd_4187261 : Nat := 2150077518826047055780643

theorem tailTrace_4187261 : CollatzResearch.WordTrace tailWord_4187261 prefixEnd_4187261 2150077518826047055780643 := by
  unfold tailWord_4187261
  simp only [CollatzResearch.WordTrace]
  refine ⟨152721955283275999089721637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101814636855517332726481091 152721955283275999089721637)
  ·
    refine ⟨28635366615614249829322807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152721955283275999089721637 28635366615614249829322807)
    ·
      refine ⟨42953049923421374743984211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28635366615614249829322807 42953049923421374743984211)
      ·
        refine ⟨64429574885132062115976317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42953049923421374743984211 64429574885132062115976317)
        ·
          refine ⟨24161090581924523293491119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64429574885132062115976317 24161090581924523293491119)
          ·
            refine ⟨36241635872886784940236679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24161090581924523293491119 36241635872886784940236679)
            ·
              refine ⟨54362453809330177410355019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36241635872886784940236679 54362453809330177410355019)
              ·
                refine ⟨81543680713995266115532529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54362453809330177410355019 81543680713995266115532529)
                ·
                  refine ⟨61157760535496449586649397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81543680713995266115532529 61157760535496449586649397)
                  ·
                    refine ⟨5733540050202792148748381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61157760535496449586649397 5733540050202792148748381)
                    ·
                      refine ⟨2150077518826047055780643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5733540050202792148748381 2150077518826047055780643)
                      ·
                        rfl

theorem cell23_4187261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_4187261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187261 prefixEnd_4187261 := by exact prefixLift 4187261
  have htrace : WordTrace (prefixWord ++ tailWord_4187261) baseStart_4187261 baseEnd_4187261 := by
    simpa [prefixWord, tailWord_4187261, baseEnd_4187261] using wordTrace_append hprefix tailTrace_4187261
  have hstable : (prefixWord ++ tailWord_4187261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187261).length < 2 ^ (prefixWord ++ tailWord_4187261).sum := by decide
  have hdescent : baseEnd_4187261 < baseStart_4187261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187328 : List Nat := [2, 1, 1, 2, 6, 1, 1, 2, 1, 6]
def baseStart_4187328 : Nat := 118140960795 + 4187328 * 2 ^ 59
def prefixEnd_4187328 : Nat := 4983230072969 + 3 ^ 40 * 4187328 * 2
def baseEnd_4187328 : Nat := 716703974009966097880945

theorem tailTrace_4187328 : CollatzResearch.WordTrace tailWord_4187328 prefixEnd_4187328 716703974009966097880945 := by
  unfold tailWord_4187328
  simp only [CollatzResearch.WordTrace]
  refine ⟨76362199487016634766205319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101816265982688846354940425 76362199487016634766205319)
  ·
    refine ⟨114543299230524952149307979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76362199487016634766205319 114543299230524952149307979)
    ·
      refine ⟨171814948845787428223961969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114543299230524952149307979 171814948845787428223961969)
      ·
        refine ⟨128861211634340571167971477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171814948845787428223961969 128861211634340571167971477)
        ·
          refine ⟨6040369295359714273498663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128861211634340571167971477 6040369295359714273498663)
          ·
            refine ⟨9060553943039571410247995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6040369295359714273498663 9060553943039571410247995)
            ·
              refine ⟨13590830914559357115371993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9060553943039571410247995 13590830914559357115371993)
              ·
                refine ⟨10193123185919517836528995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13590830914559357115371993 10193123185919517836528995)
                ·
                  refine ⟨15289684778879276754793493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10193123185919517836528995 15289684778879276754793493)
                  ·
                    refine ⟨716703974009966097880945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15289684778879276754793493 716703974009966097880945)
                    ·
                      rfl

theorem cell23_4187328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 1, 6].length) (baseStart_4187328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187328 prefixEnd_4187328 := by exact prefixLift 4187328
  have htrace : WordTrace (prefixWord ++ tailWord_4187328) baseStart_4187328 baseEnd_4187328 := by
    simpa [prefixWord, tailWord_4187328, baseEnd_4187328] using wordTrace_append hprefix tailTrace_4187328
  have hstable : (prefixWord ++ tailWord_4187328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187328).length < 2 ^ (prefixWord ++ tailWord_4187328).sum := by decide
  have hdescent : baseEnd_4187328 < baseStart_4187328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187332 : List Nat := [2, 3, 3, 1, 3, 1, 3, 1, 1, 5]
def baseStart_4187332 : Nat := 118140960795 + 4187332 * 2 ^ 59
def prefixEnd_4187332 : Nat := 4983230072969 + 3 ^ 40 * 4187332 * 2
def baseEnd_4187332 : Nat := 716704658650838759330939

theorem tailTrace_4187332 : CollatzResearch.WordTrace tailWord_4187332 prefixEnd_4187332 716704658650838759330939 := by
  unfold tailWord_4187332
  simp only [CollatzResearch.WordTrace]
  refine ⟨76362272433009389107778125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101816363244012518810370833 76362272433009389107778125)
  ·
    refine ⟨28635852162378520915416797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76362272433009389107778125 28635852162378520915416797)
    ·
      refine ⟨10738444560891945343281299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28635852162378520915416797 10738444560891945343281299)
      ·
        refine ⟨16107666841337918014921949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10738444560891945343281299 16107666841337918014921949)
        ·
          refine ⟨6040375065501719255595731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16107666841337918014921949 6040375065501719255595731)
          ·
            refine ⟨9060562598252578883393597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6040375065501719255595731 9060562598252578883393597)
            ·
              refine ⟨3397710974344717081272599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9060562598252578883393597 3397710974344717081272599)
              ·
                refine ⟨5096566461517075621908899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3397710974344717081272599 5096566461517075621908899)
                ·
                  refine ⟨7644849692275613432863349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5096566461517075621908899 7644849692275613432863349)
                  ·
                    refine ⟨716704658650838759330939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7644849692275613432863349 716704658650838759330939)
                    ·
                      rfl

theorem cell23_4187332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_4187332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187332 prefixEnd_4187332 := by exact prefixLift 4187332
  have htrace : WordTrace (prefixWord ++ tailWord_4187332) baseStart_4187332 baseEnd_4187332 := by
    simpa [prefixWord, tailWord_4187332, baseEnd_4187332] using wordTrace_append hprefix tailTrace_4187332
  have hstable : (prefixWord ++ tailWord_4187332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187332).length < 2 ^ (prefixWord ++ tailWord_4187332).sum := by decide
  have hdescent : baseEnd_4187332 < baseStart_4187332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187338 : List Nat := [3, 1, 2, 1, 3, 2, 3, 1, 1, 1, 5]
def baseStart_4187338 : Nat := 118140960795 + 4187338 * 2 ^ 59
def prefixEnd_4187338 : Nat := 4983230072969 + 3 ^ 40 * 4187338 * 2
def baseEnd_4187338 : Nat := 2150117056836443254517789

theorem tailTrace_4187338 : CollatzResearch.WordTrace tailWord_4187338 prefixEnd_4187338 2150117056836443254517789 := by
  unfold tailWord_4187338
  simp only [CollatzResearch.WordTrace]
  refine ⟨38181190925999260310068667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101816509135998027493516445 38181190925999260310068667)
  ·
    refine ⟨57271786388998890465103001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38181190925999260310068667 57271786388998890465103001)
    ·
      refine ⟨42953839791749167848827251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57271786388998890465103001 42953839791749167848827251)
      ·
        refine ⟨64430759687623751773240877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42953839791749167848827251 64430759687623751773240877)
        ·
          refine ⟨24161534882858906914965329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64430759687623751773240877 24161534882858906914965329)
          ·
            refine ⟨18121151162144180186223997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24161534882858906914965329 18121151162144180186223997)
            ·
              refine ⟨6795431685804067569833999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18121151162144180186223997 6795431685804067569833999)
              ·
                refine ⟨10193147528706101354750999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6795431685804067569833999 10193147528706101354750999)
                ·
                  refine ⟨15289721293059152032126499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10193147528706101354750999 15289721293059152032126499)
                  ·
                    refine ⟨22934581939588728048189749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15289721293059152032126499 22934581939588728048189749)
                    ·
                      refine ⟨2150117056836443254517789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22934581939588728048189749 2150117056836443254517789)
                      ·
                        rfl

theorem cell23_4187338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_4187338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187338 prefixEnd_4187338 := by exact prefixLift 4187338
  have htrace : WordTrace (prefixWord ++ tailWord_4187338) baseStart_4187338 baseEnd_4187338 := by
    simpa [prefixWord, tailWord_4187338, baseEnd_4187338] using wordTrace_append hprefix tailTrace_4187338
  have hstable : (prefixWord ++ tailWord_4187338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187338).length < 2 ^ (prefixWord ++ tailWord_4187338).sum := by decide
  have hdescent : baseEnd_4187338 < baseStart_4187338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187365 : List Nat := [1, 3, 1, 4, 3, 1, 2, 1, 1, 2, 4]
def baseStart_4187365 : Nat := 118140960795 + 4187365 * 2 ^ 59
def prefixEnd_4187365 : Nat := 4983230072969 + 3 ^ 40 * 4187365 * 2
def baseEnd_4187365 : Nat := 2150130920814114648880165

theorem tailTrace_4187365 : CollatzResearch.WordTrace tailWord_4187365 prefixEnd_4187365 2150130920814114648880165 := by
  unfold tailWord_4187365
  simp only [CollatzResearch.WordTrace]
  refine ⟨152725748474899224851507549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101817165649932816567671699 152725748474899224851507549)
  ·
    refine ⟨57272155678087209319315331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152725748474899224851507549 57272155678087209319315331)
    ·
      refine ⟨85908233517130813978972997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57272155678087209319315331 85908233517130813978972997)
      ·
        refine ⟨16107793784462027621057437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85908233517130813978972997 16107793784462027621057437)
        ·
          refine ⟨6040422669173260357896539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16107793784462027621057437 6040422669173260357896539)
          ·
            refine ⟨9060634003759890536844809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6040422669173260357896539 9060634003759890536844809)
            ·
              refine ⟨6795475502819917902633607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9060634003759890536844809 6795475502819917902633607)
              ·
                refine ⟨10193213254229876853950411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6795475502819917902633607 10193213254229876853950411)
                ·
                  refine ⟨15289819881344815280925617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10193213254229876853950411 15289819881344815280925617)
                  ·
                    refine ⟨11467364911008611460694213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15289819881344815280925617 11467364911008611460694213)
                    ·
                      refine ⟨2150130920814114648880165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11467364911008611460694213 2150130920814114648880165)
                      ·
                        rfl

theorem cell23_4187365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_4187365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187365 prefixEnd_4187365 := by exact prefixLift 4187365
  have htrace : WordTrace (prefixWord ++ tailWord_4187365) baseStart_4187365 baseEnd_4187365 := by
    simpa [prefixWord, tailWord_4187365, baseEnd_4187365] using wordTrace_append hprefix tailTrace_4187365
  have hstable : (prefixWord ++ tailWord_4187365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187365).length < 2 ^ (prefixWord ++ tailWord_4187365).sum := by decide
  have hdescent : baseEnd_4187365 < baseStart_4187365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187401 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 4, 6]
def baseStart_4187401 : Nat := 118140960795 + 4187401 * 2 ^ 59
def prefixEnd_4187401 : Nat := 4983230072969 + 3 ^ 40 * 4187401 * 2
def baseEnd_4187401 : Nat := 716716468705892169343333

theorem tailTrace_4187401 : CollatzResearch.WordTrace tailWord_4187401 prefixEnd_4187401 716716468705892169343333 := by
  unfold tailWord_4187401
  simp only [CollatzResearch.WordTrace]
  refine ⟨152727061502768802999818057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101818041001845868666545371 152727061502768802999818057)
  ·
    refine ⟨114545296127076602249863543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152727061502768802999818057 114545296127076602249863543)
    ·
      refine ⟨171817944190614903374795315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114545296127076602249863543 171817944190614903374795315)
      ·
        refine ⟨257726916285922355062192973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171817944190614903374795315 257726916285922355062192973)
        ·
          refine ⟨96647593607220883148322365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257726916285922355062192973 96647593607220883148322365)
          ·
            refine ⟨36242847602707831180620887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96647593607220883148322365 36242847602707831180620887)
            ·
              refine ⟨54364271404061746770931331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36242847602707831180620887 54364271404061746770931331)
              ·
                refine ⟨81546407106092620156396997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54364271404061746770931331 81546407106092620156396997)
                ·
                  refine ⟨15289951332392366279324437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81546407106092620156396997 15289951332392366279324437)
                  ·
                    refine ⟨716716468705892169343333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15289951332392366279324437 716716468705892169343333)
                    ·
                      rfl

theorem cell23_4187401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 6].length) (baseStart_4187401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187401 prefixEnd_4187401 := by exact prefixLift 4187401
  have htrace : WordTrace (prefixWord ++ tailWord_4187401) baseStart_4187401 baseEnd_4187401 := by
    simpa [prefixWord, tailWord_4187401, baseEnd_4187401] using wordTrace_append hprefix tailTrace_4187401
  have hstable : (prefixWord ++ tailWord_4187401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187401).length < 2 ^ (prefixWord ++ tailWord_4187401).sum := by decide
  have hdescent : baseEnd_4187401 < baseStart_4187401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187411 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 5]
def baseStart_4187411 : Nat := 118140960795 + 4187411 * 2 ^ 59
def prefixEnd_4187411 : Nat := 4983230072969 + 3 ^ 40 * 4187411 * 2
def baseEnd_4187411 : Nat := 2150154540924221468904953

theorem tailTrace_4187411 : CollatzResearch.WordTrace tailWord_4187411 prefixEnd_4187411 2150154540924221468904953 := by
  unfold tailWord_4187411
  simp only [CollatzResearch.WordTrace]
  refine ⟨152727426232732574707682087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101818284155155049805121391 152727426232732574707682087)
  ·
    refine ⟨229091139349098862061523131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152727426232732574707682087 229091139349098862061523131)
    ·
      refine ⟨343636709023648293092284697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229091139349098862061523131 343636709023648293092284697)
      ·
        refine ⟨257727531767736219819213523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343636709023648293092284697 257727531767736219819213523)
        ·
          refine ⟨386591297651604329728820285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257727531767736219819213523 386591297651604329728820285)
          ·
            refine ⟨144971736619351623648307607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386591297651604329728820285 144971736619351623648307607)
            ·
              refine ⟨217457604929027435472461411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144971736619351623648307607 217457604929027435472461411)
              ·
                refine ⟨326186407393541153208692117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217457604929027435472461411 326186407393541153208692117)
                ·
                  refine ⟨15289987846572241556657443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 326186407393541153208692117 15289987846572241556657443)
                  ·
                    refine ⟨22934981769858362334986165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15289987846572241556657443 22934981769858362334986165)
                    ·
                      refine ⟨2150154540924221468904953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22934981769858362334986165 2150154540924221468904953)
                      ·
                        rfl

theorem cell23_4187411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_4187411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187411 prefixEnd_4187411 := by exact prefixLift 4187411
  have htrace : WordTrace (prefixWord ++ tailWord_4187411) baseStart_4187411 baseEnd_4187411 := by
    simpa [prefixWord, tailWord_4187411, baseEnd_4187411] using wordTrace_append hprefix tailTrace_4187411
  have hstable : (prefixWord ++ tailWord_4187411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187411).length < 2 ^ (prefixWord ++ tailWord_4187411).sum := by decide
  have hdescent : baseEnd_4187411 < baseStart_4187411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187418 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 2, 6]
def baseStart_4187418 : Nat := 118140960795 + 4187418 * 2 ^ 59
def prefixEnd_4187418 : Nat := 4983230072969 + 3 ^ 40 * 4187418 * 2
def baseEnd_4187418 : Nat := 716719378429600980505807

theorem tailTrace_4187418 : CollatzResearch.WordTrace tailWord_4187418 prefixEnd_4187418 716719378429600980505807 := by
  unfold tailWord_4187418
  simp only [CollatzResearch.WordTrace]
  refine ⟨38181920385926803725796727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101818454362471476602124605 38181920385926803725796727)
  ·
    refine ⟨57272880578890205588695091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38181920385926803725796727 57272880578890205588695091)
    ·
      refine ⟨85909320868335308383042637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57272880578890205588695091 85909320868335308383042637)
      ·
        refine ⟨32215995325625740643640989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85909320868335308383042637 32215995325625740643640989)
        ·
          refine ⟨12080998247109652741365371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32215995325625740643640989 12080998247109652741365371)
          ·
            refine ⟨18121497370664479112048057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12080998247109652741365371 18121497370664479112048057)
            ·
              refine ⟨13591123027998359334036043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18121497370664479112048057 13591123027998359334036043)
              ·
                refine ⟨20386684541997539001054065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13591123027998359334036043 20386684541997539001054065)
                ·
                  refine ⟨15290013406498154250790549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20386684541997539001054065 15290013406498154250790549)
                  ·
                    refine ⟨716719378429600980505807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15290013406498154250790549 716719378429600980505807)
                    ·
                      rfl

theorem cell23_4187418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_4187418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187418 prefixEnd_4187418 := by exact prefixLift 4187418
  have htrace : WordTrace (prefixWord ++ tailWord_4187418) baseStart_4187418 baseEnd_4187418 := by
    simpa [prefixWord, tailWord_4187418, baseEnd_4187418] using wordTrace_append hprefix tailTrace_4187418
  have hstable : (prefixWord ++ tailWord_4187418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187418).length < 2 ^ (prefixWord ++ tailWord_4187418).sum := by decide
  have hdescent : baseEnd_4187418 < baseStart_4187418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187428 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_4187428 : Nat := 118140960795 + 4187428 * 2 ^ 59
def prefixEnd_4187428 : Nat := 4983230072969 + 3 ^ 40 * 4187428 * 2
def baseEnd_4187428 : Nat := 2150163270095347902392375

theorem tailTrace_4187428 : CollatzResearch.WordTrace tailWord_4187428 prefixEnd_4187428 2150163270095347902392375 := by
  unfold tailWord_4187428
  simp only [CollatzResearch.WordTrace]
  refine ⟨76364023136835493305525469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101818697515780657740700625 76364023136835493305525469)
  ·
    refine ⟨28636508676313309989572051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76364023136835493305525469 28636508676313309989572051)
    ·
      refine ⟨42954763014469964984358077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28636508676313309989572051 42954763014469964984358077)
      ·
        refine ⟨16108036130426236869134279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42954763014469964984358077 16108036130426236869134279)
        ·
          refine ⟨24162054195639355303701419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16108036130426236869134279 24162054195639355303701419)
          ·
            refine ⟨36243081293459032955552129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24162054195639355303701419 36243081293459032955552129)
            ·
              refine ⟨27182310970094274716664097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36243081293459032955552129 27182310970094274716664097)
              ·
                refine ⟨20386733227570706037498073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27182310970094274716664097 20386733227570706037498073)
                ·
                  refine ⟨15290049920678029528123555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20386733227570706037498073 15290049920678029528123555)
                  ·
                    refine ⟨22935074881017044292185333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15290049920678029528123555 22935074881017044292185333)
                    ·
                      refine ⟨2150163270095347902392375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22935074881017044292185333 2150163270095347902392375)
                      ·
                        rfl

theorem cell23_4187428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_4187428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187428 prefixEnd_4187428 := by exact prefixLift 4187428
  have htrace : WordTrace (prefixWord ++ tailWord_4187428) baseStart_4187428 baseEnd_4187428 := by
    simpa [prefixWord, tailWord_4187428, baseEnd_4187428] using wordTrace_append hprefix tailTrace_4187428
  have hstable : (prefixWord ++ tailWord_4187428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187428).length < 2 ^ (prefixWord ++ tailWord_4187428).sum := by decide
  have hdescent : baseEnd_4187428 < baseStart_4187428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187442 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2]
def baseStart_4187442 : Nat := 118140960795 + 4187442 * 2 ^ 59
def prefixEnd_4187442 : Nat := 4983230072969 + 3 ^ 40 * 4187442 * 2
def baseEnd_4187442 : Nat := 2150170458824510847617311

theorem tailTrace_4187442 : CollatzResearch.WordTrace tailWord_4187442 prefixEnd_4187442 2150170458824510847617311 := by
  unfold tailWord_4187442
  simp only [CollatzResearch.WordTrace]
  refine ⟨38182139223905066750515145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101819037930413511334707053 38182139223905066750515145)
  ·
    refine ⟨28636604417928800062886359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38182139223905066750515145 28636604417928800062886359)
    ·
      refine ⟨42954906626893200094329539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28636604417928800062886359 42954906626893200094329539)
      ·
        refine ⟨64432359940339800141494309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42954906626893200094329539 64432359940339800141494309)
        ·
          refine ⟨12081067488813712526530183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64432359940339800141494309 12081067488813712526530183)
          ·
            refine ⟨18121601233220568789795275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12081067488813712526530183 18121601233220568789795275)
            ·
              refine ⟨27182401849830853184692913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18121601233220568789795275 27182401849830853184692913)
              ·
                refine ⟨20386801387373139888519685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27182401849830853184692913 20386801387373139888519685)
                ·
                  refine ⟨3822525260132463729097441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20386801387373139888519685 3822525260132463729097441)
                  ·
                    refine ⟨2866893945099347796823081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3822525260132463729097441 2866893945099347796823081)
                    ·
                      refine ⟨2150170458824510847617311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2866893945099347796823081 2150170458824510847617311)
                      ·
                        rfl

theorem cell23_4187442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_4187442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187442 prefixEnd_4187442 := by exact prefixLift 4187442
  have htrace : WordTrace (prefixWord ++ tailWord_4187442) baseStart_4187442 baseEnd_4187442 := by
    simpa [prefixWord, tailWord_4187442, baseEnd_4187442] using wordTrace_append hprefix tailTrace_4187442
  have hstable : (prefixWord ++ tailWord_4187442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187442).length < 2 ^ (prefixWord ++ tailWord_4187442).sum := by decide
  have hdescent : baseEnd_4187442 < baseStart_4187442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187515 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 2, 4, 2]
def baseStart_4187515 : Nat := 118140960795 + 4187515 * 2 ^ 59
def prefixEnd_4187515 : Nat := 4983230072969 + 3 ^ 40 * 4187515 * 2
def baseEnd_4187515 : Nat := 2150207942912289062004475

theorem tailTrace_4187515 : CollatzResearch.WordTrace tailWord_4187515 prefixEnd_4187515 2150207942912289062004475 := by
  unfold tailWord_4187515
  simp only [CollatzResearch.WordTrace]
  refine ⟨152731219424355800469467999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101820812949570533646311999 152731219424355800469467999)
  ·
    refine ⟨229096829136533700704201999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152731219424355800469467999 229096829136533700704201999)
    ·
      refine ⟨343645243704800551056302999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229096829136533700704201999 343645243704800551056302999)
      ·
        refine ⟨515467865557200826584454499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343645243704800551056302999 515467865557200826584454499)
        ·
          refine ⟨773201798335801239876681749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515467865557200826584454499 773201798335801239876681749)
          ·
            refine ⟨36243834296990683119219457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 773201798335801239876681749 36243834296990683119219457)
            ·
              refine ⟨27182875722743012339414593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36243834296990683119219457 27182875722743012339414593)
              ·
                refine ⟨20387156792057259254560945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27182875722743012339414593 20387156792057259254560945)
                ·
                  refine ⟨15290367594042944440920709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20387156792057259254560945 15290367594042944440920709)
                  ·
                    refine ⟨2866943923883052082672633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15290367594042944440920709 2866943923883052082672633)
                    ·
                      refine ⟨2150207942912289062004475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2866943923883052082672633 2150207942912289062004475)
                      ·
                        rfl

theorem cell23_4187515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 4, 2].length) (baseStart_4187515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187515 prefixEnd_4187515 := by exact prefixLift 4187515
  have htrace : WordTrace (prefixWord ++ tailWord_4187515) baseStart_4187515 baseEnd_4187515 := by
    simpa [prefixWord, tailWord_4187515, baseEnd_4187515] using wordTrace_append hprefix tailTrace_4187515
  have hstable : (prefixWord ++ tailWord_4187515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187515).length < 2 ^ (prefixWord ++ tailWord_4187515).sum := by decide
  have hdescent : baseEnd_4187515 < baseStart_4187515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187522 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_4187522 : Nat := 118140960795 + 4187522 * 2 ^ 59
def prefixEnd_4187522 : Nat := 4983230072969 + 3 ^ 40 * 4187522 * 2
def baseEnd_4187522 : Nat := 2150211537276870534616943

theorem tailTrace_4187522 : CollatzResearch.WordTrace tailWord_4187522 prefixEnd_4187522 2150211537276870534616943 := by
  unfold tailWord_4187522
  simp only [CollatzResearch.WordTrace]
  refine ⟨38182868683832610166243205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101820983156886960443315213 38182868683832610166243205)
  ·
    refine ⟨7159287878218614406170601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38182868683832610166243205 7159287878218614406170601)
    ·
      refine ⟨5369465908663960804627951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7159287878218614406170601 5369465908663960804627951)
      ·
        refine ⟨8054198862995941206941927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5369465908663960804627951 8054198862995941206941927)
        ·
          refine ⟨12081298294493911810412891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8054198862995941206941927 12081298294493911810412891)
          ·
            refine ⟨18121947441740867715619337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12081298294493911810412891 18121947441740867715619337)
            ·
              refine ⟨13591460581305650786714503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18121947441740867715619337 13591460581305650786714503)
              ·
                refine ⟨20387190871958476180071755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13591460581305650786714503 20387190871958476180071755)
                ·
                  refine ⟨30580786307937714270107633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20387190871958476180071755 30580786307937714270107633)
                  ·
                    refine ⟨22935589730953285702580725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30580786307937714270107633 22935589730953285702580725)
                    ·
                      refine ⟨2150211537276870534616943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22935589730953285702580725 2150211537276870534616943)
                      ·
                        rfl

theorem cell23_4187522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_4187522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187522 prefixEnd_4187522 := by exact prefixLift 4187522
  have htrace : WordTrace (prefixWord ++ tailWord_4187522) baseStart_4187522 baseEnd_4187522 := by
    simpa [prefixWord, tailWord_4187522, baseEnd_4187522] using wordTrace_append hprefix tailTrace_4187522
  have hstable : (prefixWord ++ tailWord_4187522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187522).length < 2 ^ (prefixWord ++ tailWord_4187522).sum := by decide
  have hdescent : baseEnd_4187522 < baseStart_4187522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187559 : List Nat := [1, 1, 6, 1, 1, 1, 4, 3, 1, 4]
def baseStart_4187559 : Nat := 118140960795 + 4187559 * 2 ^ 59
def prefixEnd_4187559 : Nat := 4983230072969 + 3 ^ 40 * 4187559 * 2
def baseEnd_4187559 : Nat := 716743512020362296618091

theorem tailTrace_4187559 : CollatzResearch.WordTrace tailWord_4187559 prefixEnd_4187559 716743512020362296618091 := by
  unfold tailWord_4187559
  simp only [CollatzResearch.WordTrace]
  refine ⟨152732824236196395984069731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101821882824130930656046487 152732824236196395984069731)
  ·
    refine ⟨229099236354294593976104597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152732824236196395984069731 229099236354294593976104597)
    ·
      refine ⟨10739026704107559092629903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 229099236354294593976104597 10739026704107559092629903)
      ·
        refine ⟨16108540056161338638944855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10739026704107559092629903 16108540056161338638944855)
        ·
          refine ⟨24162810084242007958417283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16108540056161338638944855 24162810084242007958417283)
          ·
            refine ⟨36244215126363011937625925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24162810084242007958417283 36244215126363011937625925)
            ·
              refine ⟨6795790336193064738304861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36244215126363011937625925 6795790336193064738304861)
              ·
                refine ⟨2548421376072399276864323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6795790336193064738304861 2548421376072399276864323)
                ·
                  refine ⟨3822632064108598915296485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2548421376072399276864323 3822632064108598915296485)
                  ·
                    refine ⟨716743512020362296618091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3822632064108598915296485 716743512020362296618091)
                    ·
                      rfl

theorem cell23_4187559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_4187559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187559 prefixEnd_4187559 := by exact prefixLift 4187559
  have htrace : WordTrace (prefixWord ++ tailWord_4187559) baseStart_4187559 baseEnd_4187559 := by
    simpa [prefixWord, tailWord_4187559, baseEnd_4187559] using wordTrace_append hprefix tailTrace_4187559
  have hstable : (prefixWord ++ tailWord_4187559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187559).length < 2 ^ (prefixWord ++ tailWord_4187559).sum := by decide
  have hdescent : baseEnd_4187559 < baseStart_4187559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187568 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 5, 5]
def baseStart_4187568 : Nat := 118140960795 + 4187568 * 2 ^ 59
def prefixEnd_4187568 : Nat := 4983230072969 + 3 ^ 40 * 4187568 * 2
def baseEnd_4187568 : Nat := 716745052462325784880577

theorem tailTrace_4187568 : CollatzResearch.WordTrace tailWord_4187568 prefixEnd_4187568 716745052462325784880577 := by
  unfold tailWord_4187568
  simp only [CollatzResearch.WordTrace]
  refine ⟨76366576246581895260573679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101822101662109193680764905 76366576246581895260573679)
  ·
    refine ⟨114549864369872842890860519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76366576246581895260573679 114549864369872842890860519)
    ·
      refine ⟨171824796554809264336290779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114549864369872842890860519 171824796554809264336290779)
      ·
        refine ⟨257737194832213896504436169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171824796554809264336290779 257737194832213896504436169)
        ·
          refine ⟨193302896124160422378327127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257737194832213896504436169 193302896124160422378327127)
          ·
            refine ⟨289954344186240633567490691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193302896124160422378327127 289954344186240633567490691)
            ·
              refine ⟨434931516279360950351236037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289954344186240633567490691 434931516279360950351236037)
              ·
                refine ⟨81549659302380178190856757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 434931516279360950351236037 81549659302380178190856757)
                ·
                  refine ⟨7645280559598141705392821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81549659302380178190856757 7645280559598141705392821)
                  ·
                    refine ⟨716745052462325784880577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7645280559598141705392821 716745052462325784880577)
                    ·
                      rfl

theorem cell23_4187568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 5, 5].length) (baseStart_4187568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187568 prefixEnd_4187568 := by exact prefixLift 4187568
  have htrace : WordTrace (prefixWord ++ tailWord_4187568) baseStart_4187568 baseEnd_4187568 := by
    simpa [prefixWord, tailWord_4187568, baseEnd_4187568] using wordTrace_append hprefix tailTrace_4187568
  have hstable : (prefixWord ++ tailWord_4187568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187568).length < 2 ^ (prefixWord ++ tailWord_4187568).sum := by decide
  have hdescent : baseEnd_4187568 < baseStart_4187568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187615 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 6, 4]
def baseStart_4187615 : Nat := 118140960795 + 4187615 * 2 ^ 59
def prefixEnd_4187615 : Nat := 4983230072969 + 3 ^ 40 * 4187615 * 2
def baseEnd_4187615 : Nat := 716753096992579556918005

theorem tailTrace_4187615 : CollatzResearch.WordTrace tailWord_4187615 prefixEnd_4187615 716753096992579556918005 := by
  unfold tailWord_4187615
  simp only [CollatzResearch.WordTrace]
  refine ⟨152734866723993517548108299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101823244482662345032072199 152734866723993517548108299)
  ·
    refine ⟨229102300085990276322162449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152734866723993517548108299 229102300085990276322162449)
    ·
      refine ⟨171826725064492707241621837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229102300085990276322162449 171826725064492707241621837)
      ·
        refine ⟨64435021899184765215608189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171826725064492707241621837 64435021899184765215608189)
        ·
          refine ⟨24163133212194286955853071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64435021899184765215608189 24163133212194286955853071)
          ·
            refine ⟨36244699818291430433779607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24163133212194286955853071 36244699818291430433779607)
            ·
              refine ⟨54367049727437145650669411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36244699818291430433779607 54367049727437145650669411)
              ·
                refine ⟨81550574591155718476004117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54367049727437145650669411 81550574591155718476004117)
                ·
                  refine ⟨3822683183960424303562693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81550574591155718476004117 3822683183960424303562693)
                  ·
                    refine ⟨716753096992579556918005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3822683183960424303562693 716753096992579556918005)
                    ·
                      rfl

theorem cell23_4187615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 4].length) (baseStart_4187615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187615 prefixEnd_4187615 := by exact prefixLift 4187615
  have htrace : WordTrace (prefixWord ++ tailWord_4187615) baseStart_4187615 baseEnd_4187615 := by
    simpa [prefixWord, tailWord_4187615, baseEnd_4187615] using wordTrace_append hprefix tailTrace_4187615
  have hstable : (prefixWord ++ tailWord_4187615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187615).length < 2 ^ (prefixWord ++ tailWord_4187615).sum := by decide
  have hdescent : baseEnd_4187615 < baseStart_4187615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187645 : List Nat := [1, 4, 1, 1, 1, 5, 2, 8]
def baseStart_4187645 : Nat := 118140960795 + 4187645 * 2 ^ 59
def prefixEnd_4187645 : Nat := 4983230072969 + 3 ^ 40 * 4187645 * 2
def baseEnd_4187645 : Nat := 79639803533236057532551

theorem tailTrace_4187645 : CollatzResearch.WordTrace tailWord_4187645 prefixEnd_4187645 79639803533236057532551 := by
  unfold tailWord_4187645
  simp only [CollatzResearch.WordTrace]
  refine ⟨152735960913884832671700389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101823973942589888447800259 152735960913884832671700389)
  ·
    refine ⟨28637992671353406125943823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152735960913884832671700389 28637992671353406125943823)
    ·
      refine ⟨42956989007030109188915735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28637992671353406125943823 42956989007030109188915735)
      ·
        refine ⟨64435483510545163783373603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42956989007030109188915735 64435483510545163783373603)
        ·
          refine ⟨96653225265817745675060405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64435483510545163783373603 96653225265817745675060405)
          ·
            refine ⟨9061239868670413657036913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96653225265817745675060405 9061239868670413657036913)
            ·
              refine ⟨6795929901502810242777685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9061239868670413657036913 6795929901502810242777685)
              ·
                refine ⟨79639803533236057532551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6795929901502810242777685 79639803533236057532551)
                ·
                  rfl

theorem cell23_4187645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 8].length) (baseStart_4187645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187645 prefixEnd_4187645 := by exact prefixLift 4187645
  have htrace : WordTrace (prefixWord ++ tailWord_4187645) baseStart_4187645 baseEnd_4187645 := by
    simpa [prefixWord, tailWord_4187645, baseEnd_4187645] using wordTrace_append hprefix tailTrace_4187645
  have hstable : (prefixWord ++ tailWord_4187645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187645).length < 2 ^ (prefixWord ++ tailWord_4187645).sum := by decide
  have hdescent : baseEnd_4187645 < baseStart_4187645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187649 : List Nat := [1, 2, 4, 1, 4, 1, 1, 3, 2, 4]
def baseStart_4187649 : Nat := 118140960795 + 4187649 * 2 ^ 59
def prefixEnd_4187649 : Nat := 4983230072969 + 3 ^ 40 * 4187649 * 2
def baseEnd_4187649 : Nat := 716758916439997179242953

theorem tailTrace_4187649 : CollatzResearch.WordTrace tailWord_4187649 prefixEnd_4187649 716758916439997179242953 := by
  unfold tailWord_4187649
  simp only [CollatzResearch.WordTrace]
  refine ⟨152736106805870341354846001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101824071203913560903230667 152736106805870341354846001)
  ·
    refine ⟨114552080104402756016134501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152736106805870341354846001 114552080104402756016134501)
    ·
      refine ⟨21478515019575516753025219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114552080104402756016134501 21478515019575516753025219)
      ·
        refine ⟨32217772529363275129537829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21478515019575516753025219 32217772529363275129537829)
        ·
          refine ⟨6040832349255614086788343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32217772529363275129537829 6040832349255614086788343)
          ·
            refine ⟨9061248523883421130182515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6040832349255614086788343 9061248523883421130182515)
            ·
              refine ⟨13591872785825131695273773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9061248523883421130182515 13591872785825131695273773)
              ·
                refine ⟨5096952294684424385727665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13591872785825131695273773 5096952294684424385727665)
                ·
                  refine ⟨3822714221013318289295749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5096952294684424385727665 3822714221013318289295749)
                  ·
                    refine ⟨716758916439997179242953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3822714221013318289295749 716758916439997179242953)
                    ·
                      rfl

theorem cell23_4187649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_4187649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187649 prefixEnd_4187649 := by exact prefixLift 4187649
  have htrace : WordTrace (prefixWord ++ tailWord_4187649) baseStart_4187649 baseEnd_4187649 := by
    simpa [prefixWord, tailWord_4187649, baseEnd_4187649] using wordTrace_append hprefix tailTrace_4187649
  have hstable : (prefixWord ++ tailWord_4187649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187649).length < 2 ^ (prefixWord ++ tailWord_4187649).sum := by decide
  have hdescent : baseEnd_4187649 < baseStart_4187649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187705 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 1, 8]
def baseStart_4187705 : Nat := 118140960795 + 4187705 * 2 ^ 59
def prefixEnd_4187705 : Nat := 4983230072969 + 3 ^ 40 * 4187705 * 2
def baseEnd_4187705 : Nat := 716768501412214439542867

theorem tailTrace_4187705 : CollatzResearch.WordTrace tailWord_4187705 prefixEnd_4187705 716768501412214439542867 := by
  unfold tailWord_4187705
  simp only [CollatzResearch.WordTrace]
  refine ⟨152738149293667462918884569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101825432862444975279256379 152738149293667462918884569)
  ·
    refine ⟨114553611970250597189163427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152738149293667462918884569 114553611970250597189163427)
    ·
      refine ⟨171830417955375895783745141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114553611970250597189163427 171830417955375895783745141)
      ·
        refine ⟨16109101683316490229726107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171830417955375895783745141 16109101683316490229726107)
        ·
          refine ⟨24163652524974735344589161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16109101683316490229726107 24163652524974735344589161)
          ·
            refine ⟨18122739393731051508441871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24163652524974735344589161 18122739393731051508441871)
            ·
              refine ⟨27184109090596577262662807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18122739393731051508441871 27184109090596577262662807)
              ·
                refine ⟨40776163635894865893994211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27184109090596577262662807 40776163635894865893994211)
                ·
                  refine ⟨61164245453842298840991317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40776163635894865893994211 61164245453842298840991317)
                  ·
                    refine ⟨716768501412214439542867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61164245453842298840991317 716768501412214439542867)
                    ·
                      rfl

theorem cell23_4187705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 8].length) (baseStart_4187705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187705 prefixEnd_4187705 := by exact prefixLift 4187705
  have htrace : WordTrace (prefixWord ++ tailWord_4187705) baseStart_4187705 baseEnd_4187705 := by
    simpa [prefixWord, tailWord_4187705, baseEnd_4187705] using wordTrace_append hprefix tailTrace_4187705
  have hstable : (prefixWord ++ tailWord_4187705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187705).length < 2 ^ (prefixWord ++ tailWord_4187705).sum := by decide
  have hdescent : baseEnd_4187705 < baseStart_4187705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187729 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 4, 2, 2]
def baseStart_4187729 : Nat := 118140960795 + 4187729 * 2 ^ 59
def prefixEnd_4187729 : Nat := 4983230072969 + 3 ^ 40 * 4187729 * 2
def baseEnd_4187729 : Nat := 2150317827772351224728491

theorem tailTrace_4187729 : CollatzResearch.WordTrace tailWord_4187729 prefixEnd_4187729 2150317827772351224728491 := by
  unfold tailWord_4187729
  simp only [CollatzResearch.WordTrace]
  refine ⟨152739024645580515017758241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101826016430387010011838827 152739024645580515017758241)
  ·
    refine ⟨114554268484185386263318681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152739024645580515017758241 114554268484185386263318681)
    ·
      refine ⟨85915701363139039697489011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114554268484185386263318681 85915701363139039697489011)
      ·
        refine ⟨128873552044708559546233517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85915701363139039697489011 128873552044708559546233517)
        ·
          refine ⟨48327582016765709829837569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128873552044708559546233517 48327582016765709829837569)
          ·
            refine ⟨36245686512574282372378177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48327582016765709829837569 36245686512574282372378177)
            ·
              refine ⟨27184264884430711779283633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36245686512574282372378177 27184264884430711779283633)
              ·
                refine ⟨20388198663323033834462725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27184264884430711779283633 20388198663323033834462725)
                ·
                  refine ⟨3822787249373068843961761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20388198663323033834462725 3822787249373068843961761)
                  ·
                    refine ⟨2867090437029801632971321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3822787249373068843961761 2867090437029801632971321)
                    ·
                      refine ⟨2150317827772351224728491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2867090437029801632971321 2150317827772351224728491)
                      ·
                        rfl

theorem cell23_4187729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 2, 2].length) (baseStart_4187729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187729 prefixEnd_4187729 := by exact prefixLift 4187729
  have htrace : WordTrace (prefixWord ++ tailWord_4187729) baseStart_4187729 baseEnd_4187729 := by
    simpa [prefixWord, tailWord_4187729, baseEnd_4187729] using wordTrace_append hprefix tailTrace_4187729
  have hstable : (prefixWord ++ tailWord_4187729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187729).length < 2 ^ (prefixWord ++ tailWord_4187729).sum := by decide
  have hdescent : baseEnd_4187729 < baseStart_4187729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187752 : List Nat := [2, 1, 4, 3, 1, 1, 1, 3, 7]
def baseStart_4187752 : Nat := 118140960795 + 4187752 * 2 ^ 59
def prefixEnd_4187752 : Nat := 4983230072969 + 3 ^ 40 * 4187752 * 2
def baseEnd_4187752 : Nat := 238925515314156070526765

theorem tailTrace_4187752 : CollatzResearch.WordTrace tailWord_4187752 prefixEnd_4187752 238925515314156070526765 := by
  unfold tailWord_4187752
  simp only [CollatzResearch.WordTrace]
  refine ⟨76369931762248594972922755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101826575682998126630563673 76369931762248594972922755)
  ·
    refine ⟨114554897643372892459384133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76369931762248594972922755 114554897643372892459384133)
    ·
      refine ⟨21479043308132417336134525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114554897643372892459384133 21479043308132417336134525)
      ·
        refine ⟨8054641240549656501050447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21479043308132417336134525 8054641240549656501050447)
        ·
          refine ⟨12081961860824484751575671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8054641240549656501050447 12081961860824484751575671)
          ·
            refine ⟨18122942791236727127363507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12081961860824484751575671 18122942791236727127363507)
            ·
              refine ⟨27184414186855090691045261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18122942791236727127363507 27184414186855090691045261)
              ·
                refine ⟨10194155320070659009141973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27184414186855090691045261 10194155320070659009141973)
                ·
                  refine ⟨238925515314156070526765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10194155320070659009141973 238925515314156070526765)
                  ·
                    rfl

theorem cell23_4187752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 7].length) (baseStart_4187752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187752 prefixEnd_4187752 := by exact prefixLift 4187752
  have htrace : WordTrace (prefixWord ++ tailWord_4187752) baseStart_4187752 baseEnd_4187752 := by
    simpa [prefixWord, tailWord_4187752, baseEnd_4187752] using wordTrace_append hprefix tailTrace_4187752
  have hstable : (prefixWord ++ tailWord_4187752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187752).length < 2 ^ (prefixWord ++ tailWord_4187752).sum := by decide
  have hdescent : baseEnd_4187752 < baseStart_4187752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187786 : List Nat := [3, 1, 2, 3, 2, 3, 1, 3, 5]
def baseStart_4187786 : Nat := 118140960795 + 4187786 * 2 ^ 59
def prefixEnd_4187786 : Nat := 4983230072969 + 3 ^ 40 * 4187786 * 2
def baseEnd_4187786 : Nat := 238927455129961944635081

theorem tailTrace_4187786 : CollatzResearch.WordTrace tailWord_4187786 prefixEnd_4187786 238927455129961944635081 := by
  unfold tailWord_4187786
  simp only [CollatzResearch.WordTrace]
  refine ⟨38185275901593503438145803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101827402404249342501722141 38185275901593503438145803)
  ·
    refine ⟨57277913852390255157218705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38185275901593503438145803 57277913852390255157218705)
    ·
      refine ⟨42958435389292691367914029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57277913852390255157218705 42958435389292691367914029)
      ·
        refine ⟨16109413270984759262967761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42958435389292691367914029 16109413270984759262967761)
        ·
          refine ⟨12082059953238569447225821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16109413270984759262967761 12082059953238569447225821)
          ·
            refine ⟨4530772482464463542709683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12082059953238569447225821 4530772482464463542709683)
            ·
              refine ⟨6796158723696695314064525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4530772482464463542709683 6796158723696695314064525)
              ·
                refine ⟨2548559521386260742774197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6796158723696695314064525 2548559521386260742774197)
                ·
                  refine ⟨238927455129961944635081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2548559521386260742774197 238927455129961944635081)
                  ·
                    rfl

theorem cell23_4187786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 5].length) (baseStart_4187786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187786 prefixEnd_4187786 := by exact prefixLift 4187786
  have htrace : WordTrace (prefixWord ++ tailWord_4187786) baseStart_4187786 baseEnd_4187786 := by
    simpa [prefixWord, tailWord_4187786, baseEnd_4187786] using wordTrace_append hprefix tailTrace_4187786
  have hstable : (prefixWord ++ tailWord_4187786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187786).length < 2 ^ (prefixWord ++ tailWord_4187786).sum := by decide
  have hdescent : baseEnd_4187786 < baseStart_4187786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187839 : List Nat := [1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 3]
def baseStart_4187839 : Nat := 118140960795 + 4187839 * 2 ^ 59
def prefixEnd_4187839 : Nat := 4983230072969 + 3 ^ 40 * 4187839 * 2
def baseEnd_4187839 : Nat := 2150374310644345794352985

theorem tailTrace_4187839 : CollatzResearch.WordTrace tailWord_4187839 prefixEnd_4187839 2150374310644345794352985 := by
  unfold tailWord_4187839
  simp only [CollatzResearch.WordTrace]
  refine ⟨152743036675182003804262571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101828691116788002536175047 152743036675182003804262571)
  ·
    refine ⟨229114555012773005706393857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152743036675182003804262571 229114555012773005706393857)
    ·
      refine ⟨171835916259579754279795393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229114555012773005706393857 171835916259579754279795393)
      ·
        refine ⟨128876937194684815709846545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171835916259579754279795393 128876937194684815709846545)
        ·
          refine ⟨96657702896013611782384909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128876937194684815709846545 96657702896013611782384909)
          ·
            refine ⟨36246638586005104418394341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96657702896013611782384909 36246638586005104418394341)
            ·
              refine ⟨6796244734875957078448939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36246638586005104418394341 6796244734875957078448939)
              ·
                refine ⟨10194367102313935617673409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6796244734875957078448939 10194367102313935617673409)
                ·
                  refine ⟨7645775326735451713255057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10194367102313935617673409 7645775326735451713255057)
                  ·
                    refine ⟨5734331495051588784941293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7645775326735451713255057 5734331495051588784941293)
                    ·
                      refine ⟨2150374310644345794352985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5734331495051588784941293 2150374310644345794352985)
                      ·
                        rfl

theorem cell23_4187839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_4187839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187839 prefixEnd_4187839 := by exact prefixLift 4187839
  have htrace : WordTrace (prefixWord ++ tailWord_4187839) baseStart_4187839 baseEnd_4187839 := by
    simpa [prefixWord, tailWord_4187839, baseEnd_4187839] using wordTrace_append hprefix tailTrace_4187839
  have hstable : (prefixWord ++ tailWord_4187839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187839).length < 2 ^ (prefixWord ++ tailWord_4187839).sum := by decide
  have hdescent : baseEnd_4187839 < baseStart_4187839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187872 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 3, 5]
def baseStart_4187872 : Nat := 118140960795 + 4187872 * 2 ^ 59
def prefixEnd_4187872 : Nat := 4983230072969 + 3 ^ 40 * 4187872 * 2
def baseEnd_4187872 : Nat := 716797085168648055080111

theorem tailTrace_4187872 : CollatzResearch.WordTrace tailWord_4187872 prefixEnd_4187872 716797085168648055080111 := by
  unfold tailWord_4187872
  simp only [CollatzResearch.WordTrace]
  refine ⟨76372120142031225220106935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101829493522708300293475913 76372120142031225220106935)
  ·
    refine ⟨114558180213046837830160403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76372120142031225220106935 114558180213046837830160403)
    ·
      refine ⟨171837270319570256745240605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114558180213046837830160403 171837270319570256745240605)
      ·
        refine ⟨64438976369838846279465227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171837270319570256745240605 64438976369838846279465227)
        ·
          refine ⟨96658464554758269419197841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64438976369838846279465227 96658464554758269419197841)
          ·
            refine ⟨72493848416068702064398381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96658464554758269419197841 72493848416068702064398381)
            ·
              refine ⟨27185193156025763274149393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72493848416068702064398381 27185193156025763274149393)
              ·
                refine ⟨20388894867019322455612045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27185193156025763274149393 20388894867019322455612045)
                ·
                  refine ⟨7645835575132245920854517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20388894867019322455612045 7645835575132245920854517)
                  ·
                    refine ⟨716797085168648055080111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7645835575132245920854517 716797085168648055080111)
                    ·
                      rfl

theorem cell23_4187872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 3, 5].length) (baseStart_4187872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187872 prefixEnd_4187872 := by exact prefixLift 4187872
  have htrace : WordTrace (prefixWord ++ tailWord_4187872) baseStart_4187872 baseEnd_4187872 := by
    simpa [prefixWord, tailWord_4187872, baseEnd_4187872] using wordTrace_append hprefix tailTrace_4187872
  have hstable : (prefixWord ++ tailWord_4187872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187872).length < 2 ^ (prefixWord ++ tailWord_4187872).sum := by decide
  have hdescent : baseEnd_4187872 < baseStart_4187872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187886 : List Nat := [4, 1, 2, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_4187886 : Nat := 118140960795 + 4187886 * 2 ^ 59
def prefixEnd_4187886 : Nat := 4983230072969 + 3 ^ 40 * 4187886 * 2
def baseEnd_4187886 : Nat := 2150398444235107110465269

theorem tailTrace_4187886 : CollatzResearch.WordTrace tailWord_4187886 prefixEnd_4187886 2150398444235107110465269 := by
  unfold tailWord_4187886
  simp only [CollatzResearch.WordTrace]
  refine ⟨19093093863251466353902939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101829833937341153887482341 19093093863251466353902939)
  ·
    refine ⟨28639640794877199530854409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19093093863251466353902939 28639640794877199530854409)
    ·
      refine ⟨21479730596157899648140807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28639640794877199530854409 21479730596157899648140807)
      ·
        refine ⟨32219595894236849472211211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21479730596157899648140807 32219595894236849472211211)
        ·
          refine ⟨48329393841355274208316817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32219595894236849472211211 48329393841355274208316817)
          ·
            refine ⟨36247045381016455656237613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48329393841355274208316817 36247045381016455656237613)
            ·
              refine ⟨13592642017881170871089105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36247045381016455656237613 13592642017881170871089105)
              ·
                refine ⟨10194481513410878153316829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13592642017881170871089105 10194481513410878153316829)
                ·
                  refine ⟨3822930567529079307493811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10194481513410878153316829 3822930567529079307493811)
                  ·
                    refine ⟨5734395851293618961240717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3822930567529079307493811 5734395851293618961240717)
                    ·
                      refine ⟨2150398444235107110465269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5734395851293618961240717 2150398444235107110465269)
                      ·
                        rfl

theorem cell23_4187886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_4187886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187886 prefixEnd_4187886 := by exact prefixLift 4187886
  have htrace : WordTrace (prefixWord ++ tailWord_4187886) baseStart_4187886 baseEnd_4187886 := by
    simpa [prefixWord, tailWord_4187886, baseEnd_4187886] using wordTrace_append hprefix tailTrace_4187886
  have hstable : (prefixWord ++ tailWord_4187886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187886).length < 2 ^ (prefixWord ++ tailWord_4187886).sum := by decide
  have hdescent : baseEnd_4187886 < baseStart_4187886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187906 : List Nat := [3, 4, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_4187906 : Nat := 118140960795 + 4187906 * 2 ^ 59
def prefixEnd_4187906 : Nat := 4983230072969 + 3 ^ 40 * 4187906 * 2
def baseEnd_4187906 : Nat := 716802904616065677405059

theorem tailTrace_4187906 : CollatzResearch.WordTrace tailWord_4187906 prefixEnd_4187906 716802904616065677405059 := by
  unfold tailWord_4187906
  simp only [CollatzResearch.WordTrace]
  refine ⟨38186370091484818561737893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101830320243959516164634381 38186370091484818561737893)
  ·
    refine ⟨7159944392153403480325855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38186370091484818561737893 7159944392153403480325855)
    ·
      refine ⟨10739916588230105220488783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7159944392153403480325855 10739916588230105220488783)
      ·
        refine ⟨16109874882345157830733175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10739916588230105220488783 16109874882345157830733175)
        ·
          refine ⟨24164812323517736746099763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16109874882345157830733175 24164812323517736746099763)
          ·
            refine ⟨36247218485276605119149645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24164812323517736746099763 36247218485276605119149645)
            ·
              refine ⟨13592706931978726919681117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36247218485276605119149645 13592706931978726919681117)
              ·
                refine ⟨5097265099492022594880419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13592706931978726919681117 5097265099492022594880419)
                ·
                  refine ⟨7645897649238033892320629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5097265099492022594880419 7645897649238033892320629)
                  ·
                    refine ⟨716802904616065677405059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7645897649238033892320629 716802904616065677405059)
                    ·
                      rfl

theorem cell23_4187906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_4187906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187906 prefixEnd_4187906 := by exact prefixLift 4187906
  have htrace : WordTrace (prefixWord ++ tailWord_4187906) baseStart_4187906 baseEnd_4187906 := by
    simpa [prefixWord, tailWord_4187906, baseEnd_4187906] using wordTrace_append hprefix tailTrace_4187906
  have hstable : (prefixWord ++ tailWord_4187906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187906).length < 2 ^ (prefixWord ++ tailWord_4187906).sum := by decide
  have hdescent : baseEnd_4187906 < baseStart_4187906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187919 : List Nat := [1, 1, 2, 1, 1, 1, 4, 6, 2, 4]
def baseStart_4187919 : Nat := 118140960795 + 4187919 * 2 ^ 59
def prefixEnd_4187919 : Nat := 4983230072969 + 3 ^ 40 * 4187919 * 2
def baseEnd_4187919 : Nat := 716805129698901827117539

theorem tailTrace_4187919 : CollatzResearch.WordTrace tailWord_4187919 prefixEnd_4187919 716805129698901827117539 := by
  unfold tailWord_4187919
  simp only [CollatzResearch.WordTrace]
  refine ⟨152745954514892177467174811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101830636343261451644783207 152745954514892177467174811)
  ·
    refine ⟨229118931772338266200762217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152745954514892177467174811 229118931772338266200762217)
    ·
      refine ⟨171839198829253699650571663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229118931772338266200762217 171839198829253699650571663)
      ·
        refine ⟨257758798243880549475857495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171839198829253699650571663 257758798243880549475857495)
        ·
          refine ⟨386638197365820824213786243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257758798243880549475857495 386638197365820824213786243)
          ·
            refine ⟨579957296048731236320679365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386638197365820824213786243 579957296048731236320679365)
            ·
              refine ⟨108741993009137106810127381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 579957296048731236320679365 108741993009137106810127381)
              ·
                refine ⟨5097280922303301881724721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108741993009137106810127381 5097280922303301881724721)
                ·
                  refine ⟨3822960691727476411293541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5097280922303301881724721 3822960691727476411293541)
                  ·
                    refine ⟨716805129698901827117539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3822960691727476411293541 716805129698901827117539)
                    ·
                      rfl

theorem cell23_4187919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 4].length) (baseStart_4187919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187919 prefixEnd_4187919 := by exact prefixLift 4187919
  have htrace : WordTrace (prefixWord ++ tailWord_4187919) baseStart_4187919 baseEnd_4187919 := by
    simpa [prefixWord, tailWord_4187919, baseEnd_4187919] using wordTrace_append hprefix tailTrace_4187919
  have hstable : (prefixWord ++ tailWord_4187919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187919).length < 2 ^ (prefixWord ++ tailWord_4187919).sum := by decide
  have hdescent : baseEnd_4187919 < baseStart_4187919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187932 : List Nat := [2, 2, 3, 1, 1, 2, 2, 10]
def baseStart_4187932 : Nat := 118140960795 + 4187932 * 2 ^ 59
def prefixEnd_4187932 : Nat := 4983230072969 + 3 ^ 40 * 4187932 * 2
def baseEnd_4187932 : Nat := 79645261642415330758891

theorem tailTrace_4187932 : CollatzResearch.WordTrace tailWord_4187932 prefixEnd_4187932 79645261642415330758891 := by
  unfold tailWord_4187932
  simp only [CollatzResearch.WordTrace]
  refine ⟨76373214331922540343699025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101830952442563387124932033 76373214331922540343699025)
  ·
    refine ⟨57279910748941905257774269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76373214331922540343699025 57279910748941905257774269)
    ·
      refine ⟨21479966530853214471665351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57279910748941905257774269 21479966530853214471665351)
      ·
        refine ⟨32219949796279821707498027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21479966530853214471665351 32219949796279821707498027)
        ·
          refine ⟨48329924694419732561247041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32219949796279821707498027 48329924694419732561247041)
          ·
            refine ⟨36247443520814799420935281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48329924694419732561247041 36247443520814799420935281)
            ·
              refine ⟨27185582640611099565701461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36247443520814799420935281 27185582640611099565701461)
              ·
                refine ⟨79645261642415330758891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27185582640611099565701461 79645261642415330758891)
                ·
                  rfl

theorem cell23_4187932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 10].length) (baseStart_4187932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187932 prefixEnd_4187932 := by exact prefixLift 4187932
  have htrace : WordTrace (prefixWord ++ tailWord_4187932) baseStart_4187932 baseEnd_4187932 := by
    simpa [prefixWord, tailWord_4187932, baseEnd_4187932] using wordTrace_append hprefix tailTrace_4187932
  have hstable : (prefixWord ++ tailWord_4187932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187932).length < 2 ^ (prefixWord ++ tailWord_4187932).sum := by decide
  have hdescent : baseEnd_4187932 < baseStart_4187932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187939 : List Nat := [1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 4]
def baseStart_4187939 : Nat := 118140960795 + 4187939 * 2 ^ 59
def prefixEnd_4187939 : Nat := 4983230072969 + 3 ^ 40 * 4187939 * 2
def baseEnd_4187939 : Nat := 2150425658709795403102525

theorem tailTrace_4187939 : CollatzResearch.WordTrace tailWord_4187939 prefixEnd_4187939 2150425658709795403102525 := by
  unfold tailWord_4187939
  simp only [CollatzResearch.WordTrace]
  refine ⟨152746683974819720882902871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101831122649879813921935247 152746683974819720882902871)
  ·
    refine ⟨229120025962229581324354307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152746683974819720882902871 229120025962229581324354307)
    ·
      refine ⟨343680038943344371986531461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229120025962229581324354307 343680038943344371986531461)
      ·
        refine ⟨64440007301877069747474649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343680038943344371986531461 64440007301877069747474649)
        ·
          refine ⟨48330005476407802310605987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64440007301877069747474649 48330005476407802310605987)
          ·
            refine ⟨72495008214611703465908981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48330005476407802310605987 72495008214611703465908981)
            ·
              refine ⟨6796407020119847199928967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72495008214611703465908981 6796407020119847199928967)
              ·
                refine ⟨10194610530179770799893451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6796407020119847199928967 10194610530179770799893451)
                ·
                  refine ⟨15291915795269656199840177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10194610530179770799893451 15291915795269656199840177)
                  ·
                    refine ⟨11468936846452242149880133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15291915795269656199840177 11468936846452242149880133)
                    ·
                      refine ⟨2150425658709795403102525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11468936846452242149880133 2150425658709795403102525)
                      ·
                        rfl

theorem cell23_4187939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_4187939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187939 prefixEnd_4187939 := by exact prefixLift 4187939
  have htrace : WordTrace (prefixWord ++ tailWord_4187939) baseStart_4187939 baseEnd_4187939 := by
    simpa [prefixWord, tailWord_4187939, baseEnd_4187939] using wordTrace_append hprefix tailTrace_4187939
  have hstable : (prefixWord ++ tailWord_4187939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187939).length < 2 ^ (prefixWord ++ tailWord_4187939).sum := by decide
  have hdescent : baseEnd_4187939 < baseStart_4187939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187960 : List Nat := [2, 1, 2, 1, 3, 3, 3, 3, 1, 2, 2]
def baseStart_4187960 : Nat := 118140960795 + 4187960 * 2 ^ 59
def prefixEnd_4187960 : Nat := 4983230072969 + 3 ^ 40 * 4187960 * 2
def baseEnd_4187960 : Nat := 2150436441803539820939929

theorem tailTrace_4187960 : CollatzResearch.WordTrace tailWord_4187960 prefixEnd_4187960 2150436441803539820939929 := by
  unfold tailWord_4187960
  simp only [CollatzResearch.WordTrace]
  refine ⟨76373724953871820734708667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101831633271829094312944889 76373724953871820734708667)
  ·
    refine ⟨114560587430807731102063001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76373724953871820734708667 114560587430807731102063001)
    ·
      refine ⟨85920440573105798326547251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114560587430807731102063001 85920440573105798326547251)
      ·
        refine ⟨128880660859658697489820877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85920440573105798326547251 128880660859658697489820877)
        ·
          refine ⟨48330247822372011558682829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128880660859658697489820877 48330247822372011558682829)
          ·
            refine ⟨18123842933389504334506061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48330247822372011558682829 18123842933389504334506061)
            ·
              refine ⟨6796441100021064125439773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18123842933389504334506061 6796441100021064125439773)
              ·
                refine ⟨2548665412507899047039915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6796441100021064125439773 2548665412507899047039915)
                ·
                  refine ⟨3822998118761848570559873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2548665412507899047039915 3822998118761848570559873)
                  ·
                    refine ⟨2867248589071386427919905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3822998118761848570559873 2867248589071386427919905)
                    ·
                      refine ⟨2150436441803539820939929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2867248589071386427919905 2150436441803539820939929)
                      ·
                        rfl

theorem cell23_4187960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 1, 2, 2].length) (baseStart_4187960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187960 prefixEnd_4187960 := by exact prefixLift 4187960
  have htrace : WordTrace (prefixWord ++ tailWord_4187960) baseStart_4187960 baseEnd_4187960 := by
    simpa [prefixWord, tailWord_4187960, baseEnd_4187960] using wordTrace_append hprefix tailTrace_4187960
  have hstable : (prefixWord ++ tailWord_4187960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187960).length < 2 ^ (prefixWord ++ tailWord_4187960).sum := by decide
  have hdescent : baseEnd_4187960 < baseStart_4187960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187976 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 4, 1, 3]
def baseStart_4187976 : Nat := 118140960795 + 4187976 * 2 ^ 59
def prefixEnd_4187976 : Nat := 4983230072969 + 3 ^ 40 * 4187976 * 2
def baseEnd_4187976 : Nat := 2150444657494011758339855

theorem tailTrace_4187976 : CollatzResearch.WordTrace tailWord_4187976 prefixEnd_4187976 2150444657494011758339855 := by
  unfold tailWord_4187976
  simp only [CollatzResearch.WordTrace]
  refine ⟨76374016737842838100999891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101832022317123784134666521 76374016737842838100999891)
  ·
    refine ⟨114561025106764257151499837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76374016737842838100999891 114561025106764257151499837)
    ·
      refine ⟨42960384415036596431812439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114561025106764257151499837 42960384415036596431812439)
      ·
        refine ⟨64440576622554894647718659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42960384415036596431812439 64440576622554894647718659)
        ·
          refine ⟨96660864933832341971577989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64440576622554894647718659 96660864933832341971577989)
          ·
            refine ⟨18123912175093564119670873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96660864933832341971577989 18123912175093564119670873)
            ·
              refine ⟨13592934131320173089753155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18123912175093564119670873 13592934131320173089753155)
              ·
                refine ⟨20389401196980259634629733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13592934131320173089753155 20389401196980259634629733)
                ·
                  refine ⟨3823012724433798681493075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20389401196980259634629733 3823012724433798681493075)
                  ·
                    refine ⟨5734519086650698022239613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3823012724433798681493075 5734519086650698022239613)
                    ·
                      refine ⟨2150444657494011758339855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5734519086650698022239613 2150444657494011758339855)
                      ·
                        rfl

theorem cell23_4187976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_4187976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4187976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4187976 prefixEnd_4187976 := by exact prefixLift 4187976
  have htrace : WordTrace (prefixWord ++ tailWord_4187976) baseStart_4187976 baseEnd_4187976 := by
    simpa [prefixWord, tailWord_4187976, baseEnd_4187976] using wordTrace_append hprefix tailTrace_4187976
  have hstable : (prefixWord ++ tailWord_4187976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187976).length < 2 ^ (prefixWord ++ tailWord_4187976).sum := by decide
  have hdescent : baseEnd_4187976 < baseStart_4187976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188003 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 3, 3, 2]
def baseStart_4188003 : Nat := 118140960795 + 4188003 * 2 ^ 59
def prefixEnd_4188003 : Nat := 4983230072969 + 3 ^ 40 * 4188003 * 2
def baseEnd_4188003 : Nat := 2150458521471683152702231

theorem tailTrace_4188003 : CollatzResearch.WordTrace tailWord_4188003 prefixEnd_4188003 2150458521471683152702231 := by
  unfold tailWord_4188003
  simp only [CollatzResearch.WordTrace]
  refine ⟨152749018246587859813232663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101832678831058573208821775 152749018246587859813232663)
  ·
    refine ⟨229123527369881789719848995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152749018246587859813232663 229123527369881789719848995)
    ·
      refine ⟨343685291054822684579773493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229123527369881789719848995 343685291054822684579773493)
      ·
        refine ⟨32220496036389626679353765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 343685291054822684579773493 32220496036389626679353765)
        ·
          refine ⟨6041343006823055002378831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32220496036389626679353765 6041343006823055002378831)
          ·
            refine ⟨9062014510234582503568247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6041343006823055002378831 9062014510234582503568247)
            ·
              refine ⟨13593021765351873755352371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9062014510234582503568247 13593021765351873755352371)
              ·
                refine ⟨20389532648027810633028557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13593021765351873755352371 20389532648027810633028557)
                ·
                  refine ⟨7646074743010428987385709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20389532648027810633028557 7646074743010428987385709)
                  ·
                    refine ⟨2867278028628910870269641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7646074743010428987385709 2867278028628910870269641)
                    ·
                      refine ⟨2150458521471683152702231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2867278028628910870269641 2150458521471683152702231)
                      ·
                        rfl

theorem cell23_4188003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_4188003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188003 prefixEnd_4188003 := by exact prefixLift 4188003
  have htrace : WordTrace (prefixWord ++ tailWord_4188003) baseStart_4188003 baseEnd_4188003 := by
    simpa [prefixWord, tailWord_4188003, baseEnd_4188003] using wordTrace_append hprefix tailTrace_4188003
  have hstable : (prefixWord ++ tailWord_4188003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188003).length < 2 ^ (prefixWord ++ tailWord_4188003).sum := by decide
  have hdescent : baseEnd_4188003 < baseStart_4188003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188029 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_4188029 : Nat := 118140960795 + 4188029 * 2 ^ 59
def prefixEnd_4188029 : Nat := 4983230072969 + 3 ^ 40 * 4188029 * 2
def baseEnd_4188029 : Nat := 2150471871968700050977111

theorem tailTrace_4188029 : CollatzResearch.WordTrace tailWord_4188029 prefixEnd_4188029 2150471871968700050977111 := by
  unfold tailWord_4188029
  simp only [CollatzResearch.WordTrace]
  refine ⟨152749966544493666253679141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101833311029662444169119427 152749966544493666253679141)
  ·
    refine ⟨28640618727092562422564839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152749966544493666253679141 28640618727092562422564839)
    ·
      refine ⟨42960928090638843633847259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28640618727092562422564839 42960928090638843633847259)
      ·
        refine ⟨64441392135958265450770889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42960928090638843633847259 64441392135958265450770889)
        ·
          refine ⟨48331044101968699088078167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64441392135958265450770889 48331044101968699088078167)
          ·
            refine ⟨72496566152953048632117251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48331044101968699088078167 72496566152953048632117251)
            ·
              refine ⟨108744849229429572948175877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72496566152953048632117251 108744849229429572948175877)
              ·
                refine ⟨20389659230518044927782977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108744849229429572948175877 20389659230518044927782977)
                ·
                  refine ⟨15292244422888533695837233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20389659230518044927782977 15292244422888533695837233)
                  ·
                    refine ⟨11469183317166400271877925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15292244422888533695837233 11469183317166400271877925)
                    ·
                      refine ⟨2150471871968700050977111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11469183317166400271877925 2150471871968700050977111)
                      ·
                        rfl

theorem cell23_4188029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_4188029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188029 prefixEnd_4188029 := by exact prefixLift 4188029
  have htrace : WordTrace (prefixWord ++ tailWord_4188029) baseStart_4188029 baseEnd_4188029 := by
    simpa [prefixWord, tailWord_4188029, baseEnd_4188029] using wordTrace_append hprefix tailTrace_4188029
  have hstable : (prefixWord ++ tailWord_4188029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188029).length < 2 ^ (prefixWord ++ tailWord_4188029).sum := by decide
  have hdescent : baseEnd_4188029 < baseStart_4188029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188049 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 3]
def baseStart_4188049 : Nat := 118140960795 + 4188049 * 2 ^ 59
def prefixEnd_4188049 : Nat := 4983230072969 + 3 ^ 40 * 4188049 * 2
def baseEnd_4188049 : Nat := 2150482141581789972727019

theorem tailTrace_4188049 : CollatzResearch.WordTrace tailWord_4188049 prefixEnd_4188049 2150482141581789972727019 := by
  unfold tailWord_4188049
  simp only [CollatzResearch.WordTrace]
  refine ⟨152750696004421209669407201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101833797336280806446271467 152750696004421209669407201)
  ·
    refine ⟨114563022003315907252055401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152750696004421209669407201 114563022003315907252055401)
    ·
      refine ⟨85922266502486930439041551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114563022003315907252055401 85922266502486930439041551)
      ·
        refine ⟨128883399753730395658562327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85922266502486930439041551 128883399753730395658562327)
        ·
          refine ⟨193325099630595593487843491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128883399753730395658562327 193325099630595593487843491)
          ·
            refine ⟨289987649445893390231765237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193325099630595593487843491 289987649445893390231765237)
            ·
              refine ⟨27186342135552505334227991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 289987649445893390231765237 27186342135552505334227991)
              ·
                refine ⟨40779513203328758001341987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27186342135552505334227991 40779513203328758001341987)
                ·
                  refine ⟨61169269804993137002012981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40779513203328758001341987 61169269804993137002012981)
                  ·
                    refine ⟨5734619044218106593938717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61169269804993137002012981 5734619044218106593938717)
                    ·
                      refine ⟨2150482141581789972727019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5734619044218106593938717 2150482141581789972727019)
                      ·
                        rfl

theorem cell23_4188049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_4188049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188049 prefixEnd_4188049 := by exact prefixLift 4188049
  have htrace : WordTrace (prefixWord ++ tailWord_4188049) baseStart_4188049 baseEnd_4188049 := by
    simpa [prefixWord, tailWord_4188049, baseEnd_4188049] using wordTrace_append hprefix tailTrace_4188049
  have hstable : (prefixWord ++ tailWord_4188049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188049).length < 2 ^ (prefixWord ++ tailWord_4188049).sum := by decide
  have hdescent : baseEnd_4188049 < baseStart_4188049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188050 : List Nat := [3, 2, 3, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_4188050 : Nat := 118140960795 + 4188050 * 2 ^ 59
def prefixEnd_4188050 : Nat := 4983230072969 + 3 ^ 40 * 4188050 * 2
def baseEnd_4188050 : Nat := 2150482655062444468814515

theorem tailTrace_4188050 : CollatzResearch.WordTrace tailWord_4188050 prefixEnd_4188050 2150482655062444468814515 := by
  unfold tailWord_4188050
  simp only [CollatzResearch.WordTrace]
  refine ⟨38187683119354396710048401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101833821651611724560129069 38187683119354396710048401)
  ·
    refine ⟨28640762339515797532536301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38187683119354396710048401 28640762339515797532536301)
    ·
      refine ⟨10740285877318424074701113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28640762339515797532536301 10740285877318424074701113)
      ·
        refine ⟨8055214407988818056025835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10740285877318424074701113 8055214407988818056025835)
        ·
          refine ⟨12082821611983227084038753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8055214407988818056025835 12082821611983227084038753)
          ·
            refine ⟨9062116208987420313029065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12082821611983227084038753 9062116208987420313029065)
            ·
              refine ⟨6796587156740565234771799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9062116208987420313029065 6796587156740565234771799)
              ·
                refine ⟨10194880735110847852157699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6796587156740565234771799 10194880735110847852157699)
                ·
                  refine ⟨15292321102666271778236549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10194880735110847852157699 15292321102666271778236549)
                  ·
                    refine ⟨2867310206749925958419353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15292321102666271778236549 2867310206749925958419353)
                    ·
                      refine ⟨2150482655062444468814515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2867310206749925958419353 2150482655062444468814515)
                      ·
                        rfl

theorem cell23_4188050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_4188050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188050 prefixEnd_4188050 := by exact prefixLift 4188050
  have htrace : WordTrace (prefixWord ++ tailWord_4188050) baseStart_4188050 baseEnd_4188050 := by
    simpa [prefixWord, tailWord_4188050, baseEnd_4188050] using wordTrace_append hprefix tailTrace_4188050
  have hstable : (prefixWord ++ tailWord_4188050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188050).length < 2 ^ (prefixWord ++ tailWord_4188050).sum := by decide
  have hdescent : baseEnd_4188050 < baseStart_4188050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188119 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 4]
def baseStart_4188119 : Nat := 118140960795 + 4188119 * 2 ^ 59
def prefixEnd_4188119 : Nat := 4983230072969 + 3 ^ 40 * 4188119 * 2
def baseEnd_4188119 : Nat := 2150518085227604698851697

theorem tailTrace_4188119 : CollatzResearch.WordTrace tailWord_4188119 prefixEnd_4188119 2150518085227604698851697 := by
  unfold tailWord_4188119
  simp only [CollatzResearch.WordTrace]
  refine ⟨152753249114167611624455411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101835499409445074416303607 152753249114167611624455411)
  ·
    refine ⟨229129873671251417436683117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152753249114167611624455411 229129873671251417436683117)
    ·
      refine ⟨85923702626719281538756169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229129873671251417436683117 85923702626719281538756169)
      ·
        refine ⟨64442776970039461154067127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85923702626719281538756169 64442776970039461154067127)
        ·
          refine ⟨96664165455059191731100691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64442776970039461154067127 96664165455059191731100691)
          ·
            refine ⟨144996248182588787596651037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96664165455059191731100691 144996248182588787596651037)
            ·
              refine ⟨54373593068470795348744139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144996248182588787596651037 54373593068470795348744139)
              ·
                refine ⟨81560389602706193023116209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54373593068470795348744139 81560389602706193023116209)
                ·
                  refine ⟨61170292202029644767337157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81560389602706193023116209 61170292202029644767337157)
                  ·
                    refine ⟨11469429787880558393875717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61170292202029644767337157 11469429787880558393875717)
                    ·
                      refine ⟨2150518085227604698851697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11469429787880558393875717 2150518085227604698851697)
                      ·
                        rfl

theorem cell23_4188119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_4188119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188119 prefixEnd_4188119 := by exact prefixLift 4188119
  have htrace : WordTrace (prefixWord ++ tailWord_4188119) baseStart_4188119 baseEnd_4188119 := by
    simpa [prefixWord, tailWord_4188119, baseEnd_4188119] using wordTrace_append hprefix tailTrace_4188119
  have hstable : (prefixWord ++ tailWord_4188119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188119).length < 2 ^ (prefixWord ++ tailWord_4188119).sum := by decide
  have hdescent : baseEnd_4188119 < baseStart_4188119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188124 : List Nat := [2, 2, 6, 1, 1, 2, 1, 3, 5]
def baseStart_4188124 : Nat := 118140960795 + 4188124 * 2 ^ 59
def prefixEnd_4188124 : Nat := 4983230072969 + 3 ^ 40 * 4188124 * 2
def baseEnd_4188124 : Nat := 238946739181208575476575

theorem tailTrace_4188124 : CollatzResearch.WordTrace tailWord_4188124 prefixEnd_4188124 238946739181208575476575 := by
  unfold tailWord_4188124
  simp only [CollatzResearch.WordTrace]
  refine ⟨76376715739574748739193713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101835620986099664985591617 76376715739574748739193713)
  ·
    refine ⟨57282536804681061554395285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76376715739574748739193713 57282536804681061554395285)
    ·
      refine ⟨2685118912719424760362279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57282536804681061554395285 2685118912719424760362279)
      ·
        refine ⟨4027678369079137140543419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2685118912719424760362279 4027678369079137140543419)
        ·
          refine ⟨6041517553618705710815129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4027678369079137140543419 6041517553618705710815129)
          ·
            refine ⟨4531138165214029283111347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6041517553618705710815129 4531138165214029283111347)
            ·
              refine ⟨6796707247821043924667021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4531138165214029283111347 6796707247821043924667021)
              ·
                refine ⟨2548765217932891471750133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6796707247821043924667021 2548765217932891471750133)
                ·
                  refine ⟨238946739181208575476575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2548765217932891471750133 238946739181208575476575)
                  ·
                    rfl

theorem cell23_4188124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 5].length) (baseStart_4188124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188124 prefixEnd_4188124 := by exact prefixLift 4188124
  have htrace : WordTrace (prefixWord ++ tailWord_4188124) baseStart_4188124 baseEnd_4188124 := by
    simpa [prefixWord, tailWord_4188124, baseEnd_4188124] using wordTrace_append hprefix tailTrace_4188124
  have hstable : (prefixWord ++ tailWord_4188124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188124).length < 2 ^ (prefixWord ++ tailWord_4188124).sum := by decide
  have hdescent : baseEnd_4188124 < baseStart_4188124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188129 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 8]
def baseStart_4188129 : Nat := 118140960795 + 4188129 * 2 ^ 59
def prefixEnd_4188129 : Nat := 4983230072969 + 3 ^ 40 * 4188129 * 2
def baseEnd_4188129 : Nat := 238947024448238851080739

theorem tailTrace_4188129 : CollatzResearch.WordTrace tailWord_4188129 prefixEnd_4188129 238947024448238851080739 := by
  unfold tailWord_4188129
  simp only [CollatzResearch.WordTrace]
  refine ⟨152753613844131383332319441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101835742562754255554879627 152753613844131383332319441)
  ·
    refine ⟨114565210383098537499239581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152753613844131383332319441 114565210383098537499239581)
    ·
      refine ⟨42961953893661951562214843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114565210383098537499239581 42961953893661951562214843)
      ·
        refine ⟨64442930840492927343322265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42961953893661951562214843 64442930840492927343322265)
        ·
          refine ⟨48332198130369695507491699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64442930840492927343322265 48332198130369695507491699)
          ·
            refine ⟨72498297195554543261237549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48332198130369695507491699 72498297195554543261237549)
            ·
              refine ⟨27186861448332953722964081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72498297195554543261237549 27186861448332953722964081)
              ·
                refine ⟨20390146086249715292223061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27186861448332953722964081 20390146086249715292223061)
                ·
                  refine ⟨238947024448238851080739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20390146086249715292223061 238947024448238851080739)
                  ·
                    rfl

theorem cell23_4188129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 8].length) (baseStart_4188129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188129 prefixEnd_4188129 := by exact prefixLift 4188129
  have htrace : WordTrace (prefixWord ++ tailWord_4188129) baseStart_4188129 baseEnd_4188129 := by
    simpa [prefixWord, tailWord_4188129, baseEnd_4188129] using wordTrace_append hprefix tailTrace_4188129
  have hstable : (prefixWord ++ tailWord_4188129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188129).length < 2 ^ (prefixWord ++ tailWord_4188129).sum := by decide
  have hdescent : baseEnd_4188129 < baseStart_4188129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188223 : List Nat := [1, 1, 2, 2, 3, 1, 4, 3, 2, 4]
def baseStart_4188223 : Nat := 118140960795 + 4188223 * 2 ^ 59
def prefixEnd_4188223 : Nat := 4983230072969 + 3 ^ 40 * 4188223 * 2
def baseEnd_4188223 : Nat := 716857162405224097317073

theorem tailTrace_4188223 : CollatzResearch.WordTrace tailWord_4188223 prefixEnd_4188223 716857162405224097317073 := by
  unfold tailWord_4188223
  simp only [CollatzResearch.WordTrace]
  refine ⟨152757042305790837386241323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101838028203860558257494215 152757042305790837386241323)
  ·
    refine ⟨229135563458686256079361985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152757042305790837386241323 229135563458686256079361985)
    ·
      refine ⟨171851672594014692059521489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229135563458686256079361985 171851672594014692059521489)
      ·
        refine ⟨128888754445511019044641117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171851672594014692059521489 128888754445511019044641117)
        ·
          refine ⟨48333282917066632141740419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128888754445511019044641117 48333282917066632141740419)
          ·
            refine ⟨72499924375599948212610629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48333282917066632141740419 72499924375599948212610629)
            ·
              refine ⟨13593735820424990289864493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72499924375599948212610629 13593735820424990289864493)
              ·
                refine ⟨5097650932659371358699185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13593735820424990289864493 5097650932659371358699185)
                ·
                  refine ⟨3823238199494528519024389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5097650932659371358699185 3823238199494528519024389)
                  ·
                    refine ⟨716857162405224097317073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3823238199494528519024389 716857162405224097317073)
                    ·
                      rfl

theorem cell23_4188223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 4].length) (baseStart_4188223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188223 prefixEnd_4188223 := by exact prefixLift 4188223
  have htrace : WordTrace (prefixWord ++ tailWord_4188223) baseStart_4188223 baseEnd_4188223 := by
    simpa [prefixWord, tailWord_4188223, baseEnd_4188223] using wordTrace_append hprefix tailTrace_4188223
  have hstable : (prefixWord ++ tailWord_4188223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188223).length < 2 ^ (prefixWord ++ tailWord_4188223).sum := by decide
  have hdescent : baseEnd_4188223 < baseStart_4188223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188230 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_4188230 : Nat := 118140960795 + 4188230 * 2 ^ 59
def prefixEnd_4188230 : Nat := 4983230072969 + 3 ^ 40 * 4188230 * 2
def baseEnd_4188230 : Nat := 2150575081580253764563687

theorem tailTrace_4188230 : CollatzResearch.WordTrace tailWord_4188230 prefixEnd_4188230 2150575081580253764563687 := by
  unfold tailWord_4188230
  simp only [CollatzResearch.WordTrace]
  refine ⟨4773665550523921174429567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101838198411176985054497429 4773665550523921174429567)
  ·
    refine ⟨7160498325785881761644351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4773665550523921174429567 7160498325785881761644351)
    ·
      refine ⟨10740747488678822642466527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7160498325785881761644351 10740747488678822642466527)
      ·
        refine ⟨16111121233018233963699791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10740747488678822642466527 16111121233018233963699791)
        ·
          refine ⟨24166681849527350945549687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16111121233018233963699791 24166681849527350945549687)
          ·
            refine ⟨36250022774291026418324531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24166681849527350945549687 36250022774291026418324531)
            ·
              refine ⟨54375034161436539627486797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36250022774291026418324531 54375034161436539627486797)
              ·
                refine ⟨20390637810538702360307549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54375034161436539627486797 20390637810538702360307549)
                ·
                  refine ⟨7646489178952013385115331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20390637810538702360307549 7646489178952013385115331)
                  ·
                    refine ⟨11469733768428020077672997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7646489178952013385115331 11469733768428020077672997)
                    ·
                      refine ⟨2150575081580253764563687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11469733768428020077672997 2150575081580253764563687)
                      ·
                        rfl

theorem cell23_4188230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_4188230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188230 prefixEnd_4188230 := by exact prefixLift 4188230
  have htrace : WordTrace (prefixWord ++ tailWord_4188230) baseStart_4188230 baseEnd_4188230 := by
    simpa [prefixWord, tailWord_4188230, baseEnd_4188230] using wordTrace_append hprefix tailTrace_4188230
  have hstable : (prefixWord ++ tailWord_4188230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188230).length < 2 ^ (prefixWord ++ tailWord_4188230).sum := by decide
  have hdescent : baseEnd_4188230 < baseStart_4188230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188233 : List Nat := [1, 2, 1, 1, 2, 2, 4, 4, 1, 2, 3]
def baseStart_4188233 : Nat := 118140960795 + 4188233 * 2 ^ 59
def prefixEnd_4188233 : Nat := 4983230072969 + 3 ^ 40 * 4188233 * 2
def baseEnd_4188233 : Nat := 2150576622022217252826173

theorem tailTrace_4188233 : CollatzResearch.WordTrace tailWord_4188233 prefixEnd_4188233 2150576622022217252826173 := by
  unfold tailWord_4188233
  simp only [CollatzResearch.WordTrace]
  refine ⟨152757407035754609094105353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101838271357169739396070235 152757407035754609094105353)
  ·
    refine ⟨114568055276815956820579015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152757407035754609094105353 114568055276815956820579015)
    ·
      refine ⟨171852082915223935230868523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114568055276815956820579015 171852082915223935230868523)
      ·
        refine ⟨257778124372835902846302785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171852082915223935230868523 257778124372835902846302785)
        ·
          refine ⟨193333593279626927134727089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257778124372835902846302785 193333593279626927134727089)
          ·
            refine ⟨145000194959720195351045317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193333593279626927134727089 145000194959720195351045317)
            ·
              refine ⟨27187536554947536628320997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145000194959720195351045317 27187536554947536628320997)
              ·
                refine ⟨5097663104052663117810187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27187536554947536628320997 5097663104052663117810187)
                ·
                  refine ⟨7646494656078994676715281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5097663104052663117810187 7646494656078994676715281)
                  ·
                    refine ⟨5734870992059246007536461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7646494656078994676715281 5734870992059246007536461)
                    ·
                      refine ⟨2150576622022217252826173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5734870992059246007536461 2150576622022217252826173)
                      ·
                        rfl

theorem cell23_4188233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 2, 3].length) (baseStart_4188233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188233 prefixEnd_4188233 := by exact prefixLift 4188233
  have htrace : WordTrace (prefixWord ++ tailWord_4188233) baseStart_4188233 baseEnd_4188233 := by
    simpa [prefixWord, tailWord_4188233, baseEnd_4188233] using wordTrace_append hprefix tailTrace_4188233
  have hstable : (prefixWord ++ tailWord_4188233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188233).length < 2 ^ (prefixWord ++ tailWord_4188233).sum := by decide
  have hdescent : baseEnd_4188233 < baseStart_4188233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188247 : List Nat := [1, 1, 3, 2, 2, 1, 3, 5, 1, 2, 2]
def baseStart_4188247 : Nat := 118140960795 + 4188247 * 2 ^ 59
def prefixEnd_4188247 : Nat := 4983230072969 + 3 ^ 40 * 4188247 * 2
def baseEnd_4188247 : Nat := 2150583810751380198051109

theorem tailTrace_4188247 : CollatzResearch.WordTrace tailWord_4188247 prefixEnd_4188247 2150583810751380198051109 := by
  unfold tailWord_4188247
  simp only [CollatzResearch.WordTrace]
  refine ⟨152757917657703889485114995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101838611771802592990076663 152757917657703889485114995)
  ·
    refine ⟨229136876486555834227672493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152757917657703889485114995 229136876486555834227672493)
    ·
      refine ⟨85926328682458437835377185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229136876486555834227672493 85926328682458437835377185)
      ·
        refine ⟨64444746511843828376532889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85926328682458437835377185 64444746511843828376532889)
        ·
          refine ⟨48333559883882871282399667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64444746511843828376532889 48333559883882871282399667)
          ·
            refine ⟨72500339825824306923599501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48333559883882871282399667 72500339825824306923599501)
            ·
              refine ⟨27187627434684115096349813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72500339825824306923599501 27187627434684115096349813)
              ·
                refine ⟨2548840072001635790282795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27187627434684115096349813 2548840072001635790282795)
                ·
                  refine ⟨3823260108002453685424193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2548840072001635790282795 3823260108002453685424193)
                  ·
                    refine ⟨2867445081001840264068145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3823260108002453685424193 2867445081001840264068145)
                    ·
                      refine ⟨2150583810751380198051109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2867445081001840264068145 2150583810751380198051109)
                      ·
                        rfl

theorem cell23_4188247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_4188247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188247 prefixEnd_4188247 := by exact prefixLift 4188247
  have htrace : WordTrace (prefixWord ++ tailWord_4188247) baseStart_4188247 baseEnd_4188247 := by
    simpa [prefixWord, tailWord_4188247, baseEnd_4188247] using wordTrace_append hprefix tailTrace_4188247
  have hstable : (prefixWord ++ tailWord_4188247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188247).length < 2 ^ (prefixWord ++ tailWord_4188247).sum := by decide
  have hdescent : baseEnd_4188247 < baseStart_4188247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188253 : List Nat := [1, 4, 4, 1, 1, 2, 10]
def baseStart_4188253 : Nat := 118140960795 + 4188253 * 2 ^ 59
def prefixEnd_4188253 : Nat := 4983230072969 + 3 ^ 40 * 4188253 * 2
def baseEnd_4188253 : Nat := 26550455452287742896001

theorem tailTrace_4188253 : CollatzResearch.WordTrace tailWord_4188253 prefixEnd_4188253 26550455452287742896001 := by
  unfold tailWord_4188253
  simp only [CollatzResearch.WordTrace]
  refine ⟨152758136495682152509833413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101838757663788101673222275 152758136495682152509833413)
  ·
    refine ⟨28642150592940403595593765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152758136495682152509833413 28642150592940403595593765)
    ·
      refine ⟨5370403236176325674173831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28642150592940403595593765 5370403236176325674173831)
      ·
        refine ⟨8055604854264488511260747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5370403236176325674173831 8055604854264488511260747)
        ·
          refine ⟨12083407281396732766891121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8055604854264488511260747 12083407281396732766891121)
          ·
            refine ⟨9062555461047549575168341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12083407281396732766891121 9062555461047549575168341)
            ·
              refine ⟨26550455452287742896001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9062555461047549575168341 26550455452287742896001)
              ·
                rfl

theorem cell23_4188253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 10].length) (baseStart_4188253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188253 prefixEnd_4188253 := by exact prefixLift 4188253
  have htrace : WordTrace (prefixWord ++ tailWord_4188253) baseStart_4188253 baseEnd_4188253 := by
    simpa [prefixWord, tailWord_4188253, baseEnd_4188253] using wordTrace_append hprefix tailTrace_4188253
  have hstable : (prefixWord ++ tailWord_4188253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188253).length < 2 ^ (prefixWord ++ tailWord_4188253).sum := by decide
  have hdescent : baseEnd_4188253 < baseStart_4188253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188341 : List Nat := [1, 3, 3, 4, 1, 2, 1, 2, 1, 3, 2]
def baseStart_4188341 : Nat := 118140960795 + 4188341 * 2 ^ 59
def prefixEnd_4188341 : Nat := 4983230072969 + 3 ^ 40 * 4188341 * 2
def baseEnd_4188341 : Nat := 2150632077932902830275677

theorem tailTrace_4188341 : CollatzResearch.WordTrace tailWord_4188341 prefixEnd_4188341 2150632077932902830275677 := by
  unfold tailWord_4188341
  simp only [CollatzResearch.WordTrace]
  refine ⟨152761346119363343539036877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101840897412908895692691251 152761346119363343539036877)
  ·
    refine ⟨57285504794761253827138829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152761346119363343539036877 57285504794761253827138829)
    ·
      refine ⟨21482064298035470185177061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57285504794761253827138829 21482064298035470185177061)
      ·
        refine ⟨4027887055881650659720699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21482064298035470185177061 4027887055881650659720699)
        ·
          refine ⟨6041830583822475989581049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4027887055881650659720699 6041830583822475989581049)
          ·
            refine ⟨4531372937866856992185787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6041830583822475989581049 4531372937866856992185787)
            ·
              refine ⟨6797059406800285488278681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4531372937866856992185787 6797059406800285488278681)
              ·
                refine ⟨5097794555100214116209011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6797059406800285488278681 5097794555100214116209011)
                ·
                  refine ⟨7646691832650321174313517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5097794555100214116209011 7646691832650321174313517)
                  ·
                    refine ⟨2867509437243870440367569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7646691832650321174313517 2867509437243870440367569)
                    ·
                      refine ⟨2150632077932902830275677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2867509437243870440367569 2150632077932902830275677)
                      ·
                        rfl

theorem cell23_4188341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_4188341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188341 prefixEnd_4188341 := by exact prefixLift 4188341
  have htrace : WordTrace (prefixWord ++ tailWord_4188341) baseStart_4188341 baseEnd_4188341 := by
    simpa [prefixWord, tailWord_4188341, baseEnd_4188341] using wordTrace_append hprefix tailTrace_4188341
  have hstable : (prefixWord ++ tailWord_4188341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188341).length < 2 ^ (prefixWord ++ tailWord_4188341).sum := by decide
  have hdescent : baseEnd_4188341 < baseStart_4188341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188354 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_4188354 : Nat := 118140960795 + 4188354 * 2 ^ 59
def prefixEnd_4188354 : Nat := 4983230072969 + 3 ^ 40 * 4188354 * 2
def baseEnd_4188354 : Nat := 2150638753181411279413117

theorem tailTrace_4188354 : CollatzResearch.WordTrace tailWord_4188354 prefixEnd_4188354 2150638753181411279413117 := by
  unfold tailWord_4188354
  simp only [CollatzResearch.WordTrace]
  refine ⟨38190455067079061689815029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101841213512210831172840077 38190455067079061689815029)
  ·
    refine ⟨3580355162538662033420159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38190455067079061689815029 3580355162538662033420159)
    ·
      refine ⟨5370532743807993050130239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3580355162538662033420159 5370532743807993050130239)
      ·
        refine ⟨8055799115711989575195359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5370532743807993050130239 8055799115711989575195359)
        ·
          refine ⟨12083698673567984362793039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8055799115711989575195359 12083698673567984362793039)
          ·
            refine ⟨18125548010351976544189559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12083698673567984362793039 18125548010351976544189559)
            ·
              refine ⟨27188322015527964816284339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18125548010351976544189559 27188322015527964816284339)
              ·
                refine ⟨40782483023291947224426509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27188322015527964816284339 40782483023291947224426509)
                ·
                  refine ⟨15293431133734480209159941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40782483023291947224426509 15293431133734480209159941)
                  ·
                    refine ⟨2867518337575215039217489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15293431133734480209159941 2867518337575215039217489)
                    ·
                      refine ⟨2150638753181411279413117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2867518337575215039217489 2150638753181411279413117)
                      ·
                        rfl

theorem cell23_4188354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_4188354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188354 prefixEnd_4188354 := by exact prefixLift 4188354
  have htrace : WordTrace (prefixWord ++ tailWord_4188354) baseStart_4188354 baseEnd_4188354 := by
    simpa [prefixWord, tailWord_4188354, baseEnd_4188354] using wordTrace_append hprefix tailTrace_4188354
  have hstable : (prefixWord ++ tailWord_4188354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188354).length < 2 ^ (prefixWord ++ tailWord_4188354).sum := by decide
  have hdescent : baseEnd_4188354 < baseStart_4188354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188387 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 2, 3, 3]
def baseStart_4188387 : Nat := 118140960795 + 4188387 * 2 ^ 59
def prefixEnd_4188387 : Nat := 4983230072969 + 3 ^ 40 * 4188387 * 2
def baseEnd_4188387 : Nat := 2150655698043009650300465

theorem tailTrace_4188387 : CollatzResearch.WordTrace tailWord_4188387 prefixEnd_4188387 2150655698043009650300465 := by
  unfold tailWord_4188387
  simp only [CollatzResearch.WordTrace]
  refine ⟨152763023877196693395211415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101842015918131128930140943 152763023877196693395211415)
  ·
    refine ⟨229144535815795040092817123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152763023877196693395211415 229144535815795040092817123)
    ·
      refine ⟨343716803723692560139225685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229144535815795040092817123 343716803723692560139225685)
      ·
        refine ⟨4027931293637022189131551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 343716803723692560139225685 4027931293637022189131551)
        ·
          refine ⟨6041896940455533283697327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4027931293637022189131551 6041896940455533283697327)
          ·
            refine ⟨9062845410683299925545991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6041896940455533283697327 9062845410683299925545991)
            ·
              refine ⟨13594268116024949888318987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9062845410683299925545991 13594268116024949888318987)
              ·
                refine ⟨20391402174037424832478481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13594268116024949888318987 20391402174037424832478481)
                ·
                  refine ⟨15293551630528068624358861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20391402174037424832478481 15293551630528068624358861)
                  ·
                    refine ⟨5735081861448025734134573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15293551630528068624358861 5735081861448025734134573)
                    ·
                      refine ⟨2150655698043009650300465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5735081861448025734134573 2150655698043009650300465)
                      ·
                        rfl

theorem cell23_4188387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_4188387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188387 prefixEnd_4188387 := by exact prefixLift 4188387
  have htrace : WordTrace (prefixWord ++ tailWord_4188387) baseStart_4188387 baseEnd_4188387 := by
    simpa [prefixWord, tailWord_4188387, baseEnd_4188387] using wordTrace_append hprefix tailTrace_4188387
  have hstable : (prefixWord ++ tailWord_4188387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188387).length < 2 ^ (prefixWord ++ tailWord_4188387).sum := by decide
  have hdescent : baseEnd_4188387 < baseStart_4188387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188410 : List Nat := [3, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4]
def baseStart_4188410 : Nat := 118140960795 + 4188410 * 2 ^ 59
def prefixEnd_4188410 : Nat := 4983230072969 + 3 ^ 40 * 4188410 * 2
def baseEnd_4188410 : Nat := 2150667508098063060312859

theorem tailTrace_4188410 : CollatzResearch.WordTrace tailWord_4188410 prefixEnd_4188410 2150667508098063060312859 := by
  unfold tailWord_4188410
  simp only [CollatzResearch.WordTrace]
  refine ⟨38190965689028342080824671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101842575170742245548865789 38190965689028342080824671)
  ·
    refine ⟨57286448533542513121237007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38190965689028342080824671 57286448533542513121237007)
    ·
      refine ⟨85929672800313769681855511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57286448533542513121237007 85929672800313769681855511)
      ·
        refine ⟨128894509200470654522783267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85929672800313769681855511 128894509200470654522783267)
        ·
          refine ⟨193341763800705981784174901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128894509200470654522783267 193341763800705981784174901)
          ·
            refine ⟨18125790356316185792266397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193341763800705981784174901 18125790356316185792266397)
            ·
              refine ⟨6797171383618569672099899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18125790356316185792266397 6797171383618569672099899)
              ·
                refine ⟨10195757075427854508149849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6797171383618569672099899 10195757075427854508149849)
                ·
                  refine ⟨7646817806570890881112387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10195757075427854508149849 7646817806570890881112387)
                  ·
                    refine ⟨11470226709856336321668581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7646817806570890881112387 11470226709856336321668581)
                    ·
                      refine ⟨2150667508098063060312859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11470226709856336321668581 2150667508098063060312859)
                      ·
                        rfl

theorem cell23_4188410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_4188410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188410 prefixEnd_4188410 := by exact prefixLift 4188410
  have htrace : WordTrace (prefixWord ++ tailWord_4188410) baseStart_4188410 baseEnd_4188410 := by
    simpa [prefixWord, tailWord_4188410, baseEnd_4188410] using wordTrace_append hprefix tailTrace_4188410
  have hstable : (prefixWord ++ tailWord_4188410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188410).length < 2 ^ (prefixWord ++ tailWord_4188410).sum := by decide
  have hdescent : baseEnd_4188410 < baseStart_4188410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188430 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3]
def baseStart_4188430 : Nat := 118140960795 + 4188430 * 2 ^ 59
def prefixEnd_4188430 : Nat := 4983230072969 + 3 ^ 40 * 4188430 * 2
def baseEnd_4188430 : Nat := 2150677777711152982062767

theorem tailTrace_4188430 : CollatzResearch.WordTrace tailWord_4188430 prefixEnd_4188430 2150677777711152982062767 := by
  unfold tailWord_4188430
  simp only [CollatzResearch.WordTrace]
  refine ⟨19095574027005113967378343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101843061477360607826017829 19095574027005113967378343)
  ·
    refine ⟨28643361040507670951067515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19095574027005113967378343 28643361040507670951067515)
    ·
      refine ⟨42965041560761506426601273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28643361040507670951067515 42965041560761506426601273)
      ·
        refine ⟨32223781170571129819950955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42965041560761506426601273 32223781170571129819950955)
        ·
          refine ⟨48335671755856694729926433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32223781170571129819950955 48335671755856694729926433)
          ·
            refine ⟨36251753816892521047444825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48335671755856694729926433 36251753816892521047444825)
            ·
              refine ⟨27188815362669390785583619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36251753816892521047444825 27188815362669390785583619)
              ·
                refine ⟨40783223044004086178375429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27188815362669390785583619 40783223044004086178375429)
                ·
                  refine ⟨7646854320750766158445393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40783223044004086178375429 7646854320750766158445393)
                  ·
                    refine ⟨5735140740563074618834045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7646854320750766158445393 5735140740563074618834045)
                    ·
                      refine ⟨2150677777711152982062767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5735140740563074618834045 2150677777711152982062767)
                      ·
                        rfl

theorem cell23_4188430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_4188430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188430 prefixEnd_4188430 := by exact prefixLift 4188430
  have htrace : WordTrace (prefixWord ++ tailWord_4188430) baseStart_4188430 baseEnd_4188430 := by
    simpa [prefixWord, tailWord_4188430, baseEnd_4188430] using wordTrace_append hprefix tailTrace_4188430
  have hstable : (prefixWord ++ tailWord_4188430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188430).length < 2 ^ (prefixWord ++ tailWord_4188430).sum := by decide
  have hdescent : baseEnd_4188430 < baseStart_4188430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188433 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 8]
def baseStart_4188433 : Nat := 118140960795 + 4188433 * 2 ^ 59
def prefixEnd_4188433 : Nat := 4983230072969 + 3 ^ 40 * 4188433 * 2
def baseEnd_4188433 : Nat := 238964368683679607813917

theorem tailTrace_4188433 : CollatzResearch.WordTrace tailWord_4188433 prefixEnd_4188433 238964368683679607813917 := by
  unfold tailWord_4188433
  simp only [CollatzResearch.WordTrace]
  refine ⟨152764701635030043251385953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101843134423353362167590635 152764701635030043251385953)
  ·
    refine ⟨114573526226272532438539465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152764701635030043251385953 114573526226272532438539465)
    ·
      refine ⟨85930144669704399328904599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114573526226272532438539465 85930144669704399328904599)
      ·
        refine ⟨128895217004556598993356899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85930144669704399328904599 128895217004556598993356899)
        ·
          refine ⟨193342825506834898490035349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128895217004556598993356899 193342825506834898490035349)
          ·
            refine ⟨9062944945632885866720407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 193342825506834898490035349 9062944945632885866720407)
            ·
              refine ⟨13594417418449328800080611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9062944945632885866720407 13594417418449328800080611)
              ·
                refine ⟨20391626127673993200120917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13594417418449328800080611 20391626127673993200120917)
                ·
                  refine ⟨238964368683679607813917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20391626127673993200120917 238964368683679607813917)
                  ·
                    rfl

theorem cell23_4188433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 8].length) (baseStart_4188433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188433 prefixEnd_4188433 := by exact prefixLift 4188433
  have htrace : WordTrace (prefixWord ++ tailWord_4188433) baseStart_4188433 baseEnd_4188433 := by
    simpa [prefixWord, tailWord_4188433, baseEnd_4188433] using wordTrace_append hprefix tailTrace_4188433
  have hstable : (prefixWord ++ tailWord_4188433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188433).length < 2 ^ (prefixWord ++ tailWord_4188433).sum := by decide
  have hdescent : baseEnd_4188433 < baseStart_4188433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188437 : List Nat := [1, 3, 2, 1, 2, 1, 4, 4, 1, 4]
def baseStart_4188437 : Nat := 118140960795 + 4188437 * 2 ^ 59
def prefixEnd_4188437 : Nat := 4983230072969 + 3 ^ 40 * 4188437 * 2
def baseEnd_4188437 : Nat := 716893790691911484891745

theorem tailTrace_4188437 : CollatzResearch.WordTrace tailWord_4188437 prefixEnd_4188437 716893790691911484891745 := by
  unfold tailWord_4188437
  simp only [CollatzResearch.WordTrace]
  refine ⟨152764847527015551934531565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101843231684677034623021043 152764847527015551934531565)
  ·
    refine ⟨57286817822630831975449337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152764847527015551934531565 57286817822630831975449337)
    ·
      refine ⟨42965113366973123981587003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57286817822630831975449337 42965113366973123981587003)
      ·
        refine ⟨64447670050459685972380505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42965113366973123981587003 64447670050459685972380505)
        ·
          refine ⟨48335752537844764479285379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64447670050459685972380505 48335752537844764479285379)
          ·
            refine ⟨72503628806767146718928069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48335752537844764479285379 72503628806767146718928069)
            ·
              refine ⟨13594430401268840009799013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72503628806767146718928069 13594430401268840009799013)
              ·
                refine ⟨2548955700237907501837315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13594430401268840009799013 2548955700237907501837315)
                ·
                  refine ⟨3823433550356861252755973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2548955700237907501837315 3823433550356861252755973)
                  ·
                    refine ⟨716893790691911484891745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3823433550356861252755973 716893790691911484891745)
                    ·
                      rfl

theorem cell23_4188437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_4188437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188437 prefixEnd_4188437 := by exact prefixLift 4188437
  have htrace : WordTrace (prefixWord ++ tailWord_4188437) baseStart_4188437 baseEnd_4188437 := by
    simpa [prefixWord, tailWord_4188437, baseEnd_4188437] using wordTrace_append hprefix tailTrace_4188437
  have hstable : (prefixWord ++ tailWord_4188437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188437).length < 2 ^ (prefixWord ++ tailWord_4188437).sum := by decide
  have hdescent : baseEnd_4188437 < baseStart_4188437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188463 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 3, 5]
def baseStart_4188463 : Nat := 118140960795 + 4188463 * 2 ^ 59
def prefixEnd_4188463 : Nat := 4983230072969 + 3 ^ 40 * 4188463 * 2
def baseEnd_4188463 : Nat := 716898240857583784316705

theorem tailTrace_4188463 : CollatzResearch.WordTrace tailWord_4188463 prefixEnd_4188463 716898240857583784316705 := by
  unfold tailWord_4188463
  simp only [CollatzResearch.WordTrace]
  refine ⟨152765795824921358374978043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101843863883280905583318695 152765795824921358374978043)
  ·
    refine ⟨229148693737382037562467065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152765795824921358374978043 229148693737382037562467065)
    ·
      refine ⟨171861520303036528171850299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229148693737382037562467065 171861520303036528171850299)
      ·
        refine ⟨257792280454554792257775449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171861520303036528171850299 257792280454554792257775449)
        ·
          refine ⟨193344210340916094193331587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257792280454554792257775449 193344210340916094193331587)
          ·
            refine ⟨290016315511374141289997381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193344210340916094193331587 290016315511374141289997381)
            ·
              refine ⟨54378059158382651491874509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 290016315511374141289997381 54378059158382651491874509)
              ·
                refine ⟨20391772184393494309452941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54378059158382651491874509 20391772184393494309452941)
                ·
                  refine ⟨7646914569147560366044853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20391772184393494309452941 7646914569147560366044853)
                  ·
                    refine ⟨716898240857583784316705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7646914569147560366044853 716898240857583784316705)
                    ·
                      rfl

theorem cell23_4188463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 5].length) (baseStart_4188463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188463 prefixEnd_4188463 := by exact prefixLift 4188463
  have htrace : WordTrace (prefixWord ++ tailWord_4188463) baseStart_4188463 baseEnd_4188463 := by
    simpa [prefixWord, tailWord_4188463, baseEnd_4188463] using wordTrace_append hprefix tailTrace_4188463
  have hstable : (prefixWord ++ tailWord_4188463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188463).length < 2 ^ (prefixWord ++ tailWord_4188463).sum := by decide
  have hdescent : baseEnd_4188463 < baseStart_4188463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188487 : List Nat := [1, 1, 4, 1, 2, 2, 3, 2, 2, 3, 2]
def baseStart_4188487 : Nat := 118140960795 + 4188487 * 2 ^ 59
def prefixEnd_4188487 : Nat := 4983230072969 + 3 ^ 40 * 4188487 * 2
def baseEnd_4188487 : Nat := 2150707046108459259050005

theorem tailTrace_4188487 : CollatzResearch.WordTrace tailWord_4188487 prefixEnd_4188487 2150707046108459259050005 := by
  unfold tailWord_4188487
  simp only [CollatzResearch.WordTrace]
  refine ⟨152766671176834410473851715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101844447451222940315901143 152766671176834410473851715)
  ·
    refine ⟨229150006765251615710777573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152766671176834410473851715 229150006765251615710777573)
    ·
      refine ⟨42965626268484677945770795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229150006765251615710777573 42965626268484677945770795)
      ·
        refine ⟨64448439402727016918656193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42965626268484677945770795 64448439402727016918656193)
        ·
          refine ⟨48336329552045262688992145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64448439402727016918656193 48336329552045262688992145)
          ·
            refine ⟨36252247164033947016744109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48336329552045262688992145 36252247164033947016744109)
            ·
              refine ⟨13594592686512730131279041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36252247164033947016744109 13594592686512730131279041)
              ·
                refine ⟨10195944514884547598459281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13594592686512730131279041 10195944514884547598459281)
                ·
                  refine ⟨7646958386163410698844461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10195944514884547598459281 7646958386163410698844461)
                  ·
                    refine ⟨2867609394811279012066673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7646958386163410698844461 2867609394811279012066673)
                    ·
                      refine ⟨2150707046108459259050005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2867609394811279012066673 2150707046108459259050005)
                      ·
                        rfl

theorem cell23_4188487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_4188487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188487 prefixEnd_4188487 := by exact prefixLift 4188487
  have htrace : WordTrace (prefixWord ++ tailWord_4188487) baseStart_4188487 baseEnd_4188487 := by
    simpa [prefixWord, tailWord_4188487, baseEnd_4188487] using wordTrace_append hprefix tailTrace_4188487
  have hstable : (prefixWord ++ tailWord_4188487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188487).length < 2 ^ (prefixWord ++ tailWord_4188487).sum := by decide
  have hdescent : baseEnd_4188487 < baseStart_4188487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188514 : List Nat := [3, 3, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_4188514 : Nat := 118140960795 + 4188514 * 2 ^ 59
def prefixEnd_4188514 : Nat := 4983230072969 + 3 ^ 40 * 4188514 * 2
def baseEnd_4188514 : Nat := 716906970028710217804127

theorem tailTrace_4188514 : CollatzResearch.WordTrace tailWord_4188514 prefixEnd_4188514 716906970028710217804127 := by
  unfold tailWord_4188514
  simp only [CollatzResearch.WordTrace]
  refine ⟨38191913986934148521271149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101845103965157729390056397 38191913986934148521271149)
  ·
    refine ⟨14321967745100305695476681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38191913986934148521271149 14321967745100305695476681)
    ·
      refine ⟨10741475808825229271607511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14321967745100305695476681 10741475808825229271607511)
      ·
        refine ⟨16112213713237843907411267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10741475808825229271607511 16112213713237843907411267)
        ·
          refine ⟨24168320569856765861116901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16112213713237843907411267 24168320569856765861116901)
          ·
            refine ⟨4531560106848143598959419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24168320569856765861116901 4531560106848143598959419)
            ·
              refine ⟨6797340160272215398439129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4531560106848143598959419 6797340160272215398439129)
              ·
                refine ⟨5098005120204161548829347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6797340160272215398439129 5098005120204161548829347)
                ·
                  refine ⟨7647007680306242323244021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098005120204161548829347 7647007680306242323244021)
                  ·
                    refine ⟨716906970028710217804127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7647007680306242323244021 716906970028710217804127)
                    ·
                      rfl

theorem cell23_4188514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_4188514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188514 prefixEnd_4188514 := by exact prefixLift 4188514
  have htrace : WordTrace (prefixWord ++ tailWord_4188514) baseStart_4188514 baseEnd_4188514 := by
    simpa [prefixWord, tailWord_4188514, baseEnd_4188514] using wordTrace_append hprefix tailTrace_4188514
  have hstable : (prefixWord ++ tailWord_4188514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188514).length < 2 ^ (prefixWord ++ tailWord_4188514).sum := by decide
  have hdescent : baseEnd_4188514 < baseStart_4188514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188517 : List Nat := [1, 3, 1, 3, 1, 3, 3, 2, 1, 1, 4]
def baseStart_4188517 : Nat := 118140960795 + 4188517 * 2 ^ 59
def prefixEnd_4188517 : Nat := 4983230072969 + 3 ^ 40 * 4188517 * 2
def baseEnd_4188517 : Nat := 2150722450528094141674867

theorem tailTrace_4188517 : CollatzResearch.WordTrace tailWord_4188517 prefixEnd_4188517 2150722450528094141674867 := by
  unfold tailWord_4188517
  simp only [CollatzResearch.WordTrace]
  refine ⟨152767765366725725597443805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101845176911150483731629203 152767765366725725597443805)
  ·
    refine ⟨57287912012522147099041427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152767765366725725597443805 57287912012522147099041427)
    ·
      refine ⟨85931868018783220648562141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57287912012522147099041427 85931868018783220648562141)
      ·
        refine ⟨32224450507043707743210803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85931868018783220648562141 32224450507043707743210803)
        ·
          refine ⟨48336675760565561614816205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32224450507043707743210803 48336675760565561614816205)
          ·
            refine ⟨18126253410212085605556077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48336675760565561614816205 18126253410212085605556077)
            ·
              refine ⟨6797345028829532102083529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18126253410212085605556077 6797345028829532102083529)
              ·
                refine ⟨5098008771622149076562647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6797345028829532102083529 5098008771622149076562647)
                ·
                  refine ⟨7647013157433223614843971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098008771622149076562647 7647013157433223614843971)
                  ·
                    refine ⟨11470519736149835422265957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7647013157433223614843971 11470519736149835422265957)
                    ·
                      refine ⟨2150722450528094141674867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11470519736149835422265957 2150722450528094141674867)
                      ·
                        rfl

theorem cell23_4188517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_4188517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188517 prefixEnd_4188517 := by exact prefixLift 4188517
  have htrace : WordTrace (prefixWord ++ tailWord_4188517) baseStart_4188517 baseEnd_4188517 := by
    simpa [prefixWord, tailWord_4188517, baseEnd_4188517] using wordTrace_append hprefix tailTrace_4188517
  have hstable : (prefixWord ++ tailWord_4188517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188517).length < 2 ^ (prefixWord ++ tailWord_4188517).sum := by decide
  have hdescent : baseEnd_4188517 < baseStart_4188517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188530 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_4188530 : Nat := 118140960795 + 4188530 * 2 ^ 59
def prefixEnd_4188530 : Nat := 4983230072969 + 3 ^ 40 * 4188530 * 2
def baseEnd_4188530 : Nat := 2150729125776602590812307

theorem tailTrace_4188530 : CollatzResearch.WordTrace tailWord_4188530 prefixEnd_4188530 2150729125776602590812307 := by
  unfold tailWord_4188530
  simp only [CollatzResearch.WordTrace]
  refine ⟨38192059878919657204416761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101845493010452419211778029 38192059878919657204416761)
  ·
    refine ⟨28644044909189742903312571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38192059878919657204416761 28644044909189742903312571)
    ·
      refine ⟨42966067363784614354968857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28644044909189742903312571 42966067363784614354968857)
      ·
        refine ⟨32224550522838460766226643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42966067363784614354968857 32224550522838460766226643)
        ·
          refine ⟨48336825784257691149339965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32224550522838460766226643 48336825784257691149339965)
          ·
            refine ⟨18126309669096634181002487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48336825784257691149339965 18126309669096634181002487)
            ·
              refine ⟨27189464503644951271503731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18126309669096634181002487 27189464503644951271503731)
              ·
                refine ⟨40784196755467426907255597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27189464503644951271503731 40784196755467426907255597)
                ·
                  refine ⟨15294073783300285090220849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40784196755467426907255597 15294073783300285090220849)
                  ·
                    refine ⟨11470555337475213817665637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15294073783300285090220849 11470555337475213817665637)
                    ·
                      refine ⟨2150729125776602590812307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11470555337475213817665637 2150729125776602590812307)
                      ·
                        rfl

theorem cell23_4188530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_4188530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188530 prefixEnd_4188530 := by exact prefixLift 4188530
  have htrace : WordTrace (prefixWord ++ tailWord_4188530) baseStart_4188530 baseEnd_4188530 := by
    simpa [prefixWord, tailWord_4188530, baseEnd_4188530] using wordTrace_append hprefix tailTrace_4188530
  have hstable : (prefixWord ++ tailWord_4188530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188530).length < 2 ^ (prefixWord ++ tailWord_4188530).sum := by decide
  have hdescent : baseEnd_4188530 < baseStart_4188530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188551 : List Nat := [1, 1, 4, 2, 2, 1, 3, 4, 1, 2, 2]
def baseStart_4188551 : Nat := 118140960795 + 4188551 * 2 ^ 59
def prefixEnd_4188551 : Nat := 4983230072969 + 3 ^ 40 * 4188551 * 2
def baseEnd_4188551 : Nat := 2150739908870347008649711

theorem tailTrace_4188551 : CollatzResearch.WordTrace tailWord_4188551 prefixEnd_4188551 2150739908870347008649711 := by
  unfold tailWord_4188551
  simp only [CollatzResearch.WordTrace]
  refine ⟨152769005448602549404181507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101846003632401699602787671 152769005448602549404181507)
  ·
    refine ⟨229153508172903824106272261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152769005448602549404181507 229153508172903824106272261)
    ·
      refine ⟨42966282782419467019926049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229153508172903824106272261 42966282782419467019926049)
      ·
        refine ⟨32224712086814600264944537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42966282782419467019926049 32224712086814600264944537)
        ·
          refine ⟨24168534065110950198708403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32224712086814600264944537 24168534065110950198708403)
          ·
            refine ⟨36252801097666425298062605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24168534065110950198708403 36252801097666425298062605)
            ·
              refine ⟨13594800411624909486773477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36252801097666425298062605 13594800411624909486773477)
              ·
                refine ⟨2549025077179670528770027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13594800411624909486773477 2549025077179670528770027)
                ·
                  refine ⟨3823537615769505793155041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549025077179670528770027 3823537615769505793155041)
                  ·
                    refine ⟨2867653211827129344866281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3823537615769505793155041 2867653211827129344866281)
                    ·
                      refine ⟨2150739908870347008649711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2867653211827129344866281 2150739908870347008649711)
                      ·
                        rfl

theorem cell23_4188551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_4188551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188551 prefixEnd_4188551 := by exact prefixLift 4188551
  have htrace : WordTrace (prefixWord ++ tailWord_4188551) baseStart_4188551 baseEnd_4188551 := by
    simpa [prefixWord, tailWord_4188551, baseEnd_4188551] using wordTrace_append hprefix tailTrace_4188551
  have hstable : (prefixWord ++ tailWord_4188551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188551).length < 2 ^ (prefixWord ++ tailWord_4188551).sum := by decide
  have hdescent : baseEnd_4188551 < baseStart_4188551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188564 : List Nat := [2, 4, 2, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_4188564 : Nat := 118140960795 + 4188564 * 2 ^ 59
def prefixEnd_4188564 : Nat := 4983230072969 + 3 ^ 40 * 4188564 * 2
def baseEnd_4188564 : Nat := 2150746584118855457787151

theorem tailTrace_4188564 : CollatzResearch.WordTrace tailWord_4188564 prefixEnd_4188564 2150746584118855457787151 := by
  unfold tailWord_4188564
  simp only [CollatzResearch.WordTrace]
  refine ⟨76384739798777726312202373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101846319731703635082936497 76384739798777726312202373)
  ·
    refine ⟨14322138712270823683537945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76384739798777726312202373 14322138712270823683537945)
    ·
      refine ⟨10741604034203117762653459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14322138712270823683537945 10741604034203117762653459)
      ·
        refine ⟨16112406051304676643980189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10741604034203117762653459 16112406051304676643980189)
        ·
          refine ⟨6042152269239253741492571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16112406051304676643980189 6042152269239253741492571)
          ·
            refine ⟨9063228403858880612238857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6042152269239253741492571 9063228403858880612238857)
            ·
              refine ⟨6797421302894160459179143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9063228403858880612238857 6797421302894160459179143)
              ·
                refine ⟨10196131954341240688768715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6797421302894160459179143 10196131954341240688768715)
                ·
                  refine ⟨15294197931511861033153073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10196131954341240688768715 15294197931511861033153073)
                  ·
                    refine ⟨11470648448633895774864805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15294197931511861033153073 11470648448633895774864805)
                    ·
                      refine ⟨2150746584118855457787151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11470648448633895774864805 2150746584118855457787151)
                      ·
                        rfl

theorem cell23_4188564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_4188564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188564 prefixEnd_4188564 := by exact prefixLift 4188564
  have htrace : WordTrace (prefixWord ++ tailWord_4188564) baseStart_4188564 baseEnd_4188564 := by
    simpa [prefixWord, tailWord_4188564, baseEnd_4188564] using wordTrace_append hprefix tailTrace_4188564
  have hstable : (prefixWord ++ tailWord_4188564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188564).length < 2 ^ (prefixWord ++ tailWord_4188564).sum := by decide
  have hdescent : baseEnd_4188564 < baseStart_4188564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188574 : List Nat := [4, 3, 1, 2, 1, 2, 3, 7]
def baseStart_4188574 : Nat := 118140960795 + 4188574 * 2 ^ 59
def prefixEnd_4188574 : Nat := 4983230072969 + 3 ^ 40 * 4188574 * 2
def baseEnd_4188574 : Nat := 79657471071311126617115

theorem tailTrace_4188574 : CollatzResearch.WordTrace tailWord_4188574 prefixEnd_4188574 79657471071311126617115 := by
  unfold tailWord_4188574
  simp only [CollatzResearch.WordTrace]
  refine ⟨19096230540939903041533597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101846562885012816221512517 19096230540939903041533597)
  ·
    refine ⟨7161086452852463640575099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19096230540939903041533597 7161086452852463640575099)
    ·
      refine ⟨10741629679278695460862649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7161086452852463640575099 10741629679278695460862649)
      ·
        refine ⟨8056222259459021595646987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10741629679278695460862649 8056222259459021595646987)
        ·
          refine ⟨12084333389188532393470481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8056222259459021595646987 12084333389188532393470481)
          ·
            refine ⟨9063250041891399295102861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12084333389188532393470481 9063250041891399295102861)
            ·
              refine ⟨3398718765709274735663573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9063250041891399295102861 3398718765709274735663573)
              ·
                refine ⟨79657471071311126617115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3398718765709274735663573 79657471071311126617115)
                ·
                  rfl

theorem cell23_4188574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 7].length) (baseStart_4188574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188574 prefixEnd_4188574 := by exact prefixLift 4188574
  have htrace : WordTrace (prefixWord ++ tailWord_4188574) baseStart_4188574 baseEnd_4188574 := by
    simpa [prefixWord, tailWord_4188574, baseEnd_4188574] using wordTrace_append hprefix tailTrace_4188574
  have hstable : (prefixWord ++ tailWord_4188574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188574).length < 2 ^ (prefixWord ++ tailWord_4188574).sum := by decide
  have hdescent : baseEnd_4188574 < baseStart_4188574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188584 : List Nat := [2, 1, 6, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_4188584 : Nat := 118140960795 + 4188584 * 2 ^ 59
def prefixEnd_4188584 : Nat := 4983230072969 + 3 ^ 40 * 4188584 * 2
def baseEnd_4188584 : Nat := 2150756853731945379537059

theorem tailTrace_4188584 : CollatzResearch.WordTrace tailWord_4188584 prefixEnd_4188584 2150756853731945379537059 := by
  unfold tailWord_4188584
  simp only [CollatzResearch.WordTrace]
  refine ⟨76385104528741498020066403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101846806038321997360088537 76385104528741498020066403)
  ·
    refine ⟨114577656793112247030099605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76385104528741498020066403 114577656793112247030099605)
    ·
      refine ⟨5370827662177136579535919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 114577656793112247030099605 5370827662177136579535919)
      ·
        refine ⟨8056241493265704869303879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5370827662177136579535919 8056241493265704869303879)
        ·
          refine ⟨12084362239898557303955819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8056241493265704869303879 12084362239898557303955819)
          ·
            refine ⟨18126543359847835955933729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12084362239898557303955819 18126543359847835955933729)
            ·
              refine ⟨13594907519885876966950297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18126543359847835955933729 13594907519885876966950297)
              ·
                refine ⟨10196180639914407725212723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13594907519885876966950297 10196180639914407725212723)
                ·
                  refine ⟨15294270959871611587819085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10196180639914407725212723 15294270959871611587819085)
                  ·
                    refine ⟨5735351609951854345432157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15294270959871611587819085 5735351609951854345432157)
                    ·
                      refine ⟨2150756853731945379537059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5735351609951854345432157 2150756853731945379537059)
                      ·
                        rfl

theorem cell23_4188584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_4188584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188584 prefixEnd_4188584 := by exact prefixLift 4188584
  have htrace : WordTrace (prefixWord ++ tailWord_4188584) baseStart_4188584 baseEnd_4188584 := by
    simpa [prefixWord, tailWord_4188584, baseEnd_4188584] using wordTrace_append hprefix tailTrace_4188584
  have hstable : (prefixWord ++ tailWord_4188584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188584).length < 2 ^ (prefixWord ++ tailWord_4188584).sum := by decide
  have hdescent : baseEnd_4188584 < baseStart_4188584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188594 : List Nat := [3, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2]
def baseStart_4188594 : Nat := 118140960795 + 4188594 * 2 ^ 59
def prefixEnd_4188594 : Nat := 4983230072969 + 3 ^ 40 * 4188594 * 2
def baseEnd_4188594 : Nat := 2150761988538490340412013

theorem tailTrace_4188594 : CollatzResearch.WordTrace tailWord_4188594 prefixEnd_4188594 2150761988538490340412013 := by
  unfold tailWord_4188594
  simp only [CollatzResearch.WordTrace]
  refine ⟨38192643446861691936999209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101847049191631178498664557 38192643446861691936999209)
  ·
    refine ⟨28644482585146268952749407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38192643446861691936999209 28644482585146268952749407)
    ·
      refine ⟨42966723877719403429124111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28644482585146268952749407 42966723877719403429124111)
      ·
        refine ⟨64450085816579105143686167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42966723877719403429124111 64450085816579105143686167)
        ·
          refine ⟨96675128724868657715529251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64450085816579105143686167 96675128724868657715529251)
          ·
            refine ⟨145012693087302986573293877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96675128724868657715529251 145012693087302986573293877)
            ·
              refine ⟨13594939976934654991246301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145012693087302986573293877 13594939976934654991246301)
              ·
                refine ⟨5098102491350495621717363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13594939976934654991246301 5098102491350495621717363)
                ·
                  refine ⟨7647153737025743432576045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098102491350495621717363 7647153737025743432576045)
                  ·
                    refine ⟨2867682651384653787216017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7647153737025743432576045 2867682651384653787216017)
                    ·
                      refine ⟨2150761988538490340412013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2867682651384653787216017 2150761988538490340412013)
                      ·
                        rfl

theorem cell23_4188594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_4188594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188594 prefixEnd_4188594 := by exact prefixLift 4188594
  have htrace : WordTrace (prefixWord ++ tailWord_4188594) baseStart_4188594 baseEnd_4188594 := by
    simpa [prefixWord, tailWord_4188594, baseEnd_4188594] using wordTrace_append hprefix tailTrace_4188594
  have hstable : (prefixWord ++ tailWord_4188594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188594).length < 2 ^ (prefixWord ++ tailWord_4188594).sum := by decide
  have hdescent : baseEnd_4188594 < baseStart_4188594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188601 : List Nat := [1, 2, 1, 4, 3, 3, 1, 2, 2, 1, 3]
def baseStart_4188601 : Nat := 118140960795 + 4188601 * 2 ^ 59
def prefixEnd_4188601 : Nat := 4983230072969 + 3 ^ 40 * 4188601 * 2
def baseEnd_4188601 : Nat := 2150765582903071813024481

theorem tailTrace_4188601 : CollatzResearch.WordTrace tailWord_4188601 prefixEnd_4188601 2150765582903071813024481 := by
  unfold tailWord_4188601
  simp only [CollatzResearch.WordTrace]
  refine ⟨152770829098421407943501657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101847219398947605295667771 152770829098421407943501657)
  ·
    refine ⟨114578121823816055957626243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152770829098421407943501657 114578121823816055957626243)
    ·
      refine ⟨171867182735724083936439365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114578121823816055957626243 171867182735724083936439365)
      ·
        refine ⟨32225096762948265738082381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171867182735724083936439365 32225096762948265738082381)
        ·
          refine ⟨12084411286105599651780893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32225096762948265738082381 12084411286105599651780893)
          ·
            refine ⟨4531654232289599869417835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12084411286105599651780893 4531654232289599869417835)
            ·
              refine ⟨6797481348434399804126753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4531654232289599869417835 6797481348434399804126753)
              ·
                refine ⟨5098111011325799853095065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6797481348434399804126753 5098111011325799853095065)
                ·
                  refine ⟨3823583258494349889821299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5098111011325799853095065 3823583258494349889821299)
                  ·
                    refine ⟨5735374887741524834731949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3823583258494349889821299 5735374887741524834731949)
                    ·
                      refine ⟨2150765582903071813024481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5735374887741524834731949 2150765582903071813024481)
                      ·
                        rfl

theorem cell23_4188601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_4188601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188601 prefixEnd_4188601 := by exact prefixLift 4188601
  have htrace : WordTrace (prefixWord ++ tailWord_4188601) baseStart_4188601 baseEnd_4188601 := by
    simpa [prefixWord, tailWord_4188601, baseEnd_4188601] using wordTrace_append hprefix tailTrace_4188601
  have hstable : (prefixWord ++ tailWord_4188601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188601).length < 2 ^ (prefixWord ++ tailWord_4188601).sum := by decide
  have hdescent : baseEnd_4188601 < baseStart_4188601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188664 : List Nat := [2, 1, 2, 1, 1, 4, 5, 2, 5]
def baseStart_4188664 : Nat := 118140960795 + 4188664 * 2 ^ 59
def prefixEnd_4188664 : Nat := 4983230072969 + 3 ^ 40 * 4188664 * 2
def baseEnd_4188664 : Nat := 238977548020478340726299

theorem tailTrace_4188664 : CollatzResearch.WordTrace tailWord_4188664 prefixEnd_4188664 238977548020478340726299 := by
  unfold tailWord_4188664
  simp only [CollatzResearch.WordTrace]
  refine ⟨76386563448596584851522523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101848751264795446468696697 76386563448596584851522523)
  ·
    refine ⟨114579845172894877277283785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76386563448596584851522523 114579845172894877277283785)
    ·
      refine ⟨85934883879671157957962839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114579845172894877277283785 85934883879671157957962839)
      ·
        refine ⟨128902325819506736936944259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85934883879671157957962839 128902325819506736936944259)
        ·
          refine ⟨193353488729260105405416389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128902325819506736936944259 193353488729260105405416389)
          ·
            refine ⟨36253779136736269763515573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193353488729260105405416389 36253779136736269763515573)
            ·
              refine ⟨3398791794069025290329585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36253779136736269763515573 3398791794069025290329585)
              ·
                refine ⟨2549093845551768967747189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3398791794069025290329585 2549093845551768967747189)
                ·
                  refine ⟨238977548020478340726299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2549093845551768967747189 238977548020478340726299)
                  ·
                    rfl

theorem cell23_4188664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 5].length) (baseStart_4188664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188664 prefixEnd_4188664 := by exact prefixLift 4188664
  have htrace : WordTrace (prefixWord ++ tailWord_4188664) baseStart_4188664 baseEnd_4188664 := by
    simpa [prefixWord, tailWord_4188664, baseEnd_4188664] using wordTrace_append hprefix tailTrace_4188664
  have hstable : (prefixWord ++ tailWord_4188664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188664).length < 2 ^ (prefixWord ++ tailWord_4188664).sum := by decide
  have hdescent : baseEnd_4188664 < baseStart_4188664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188697 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 1, 6, 2]
def baseStart_4188697 : Nat := 118140960795 + 4188697 * 2 ^ 59
def prefixEnd_4188697 : Nat := 4983230072969 + 3 ^ 40 * 4188697 * 2
def baseEnd_4188697 : Nat := 2150814877045903437424039

theorem tailTrace_4188697 : CollatzResearch.WordTrace tailWord_4188697 prefixEnd_4188697 2150814877045903437424039 := by
  unfold tailWord_4188697
  simp only [CollatzResearch.WordTrace]
  refine ⟨152774330506073616338996345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101849553670715744225997563 152774330506073616338996345)
  ·
    refine ⟨114580747879555212254247259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152774330506073616338996345 114580747879555212254247259)
    ·
      refine ⟨171871121819332818381370889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114580747879555212254247259 171871121819332818381370889)
      ·
        refine ⟨128903341364499613786028167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171871121819332818381370889 128903341364499613786028167)
        ·
          refine ⟨193355012046749420679042251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128903341364499613786028167 193355012046749420679042251)
          ·
            refine ⟨290032518070124131018563377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193355012046749420679042251 290032518070124131018563377)
            ·
              refine ⟨217524388552593098263922533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290032518070124131018563377 217524388552593098263922533)
              ·
                refine ⟨40785822853611205924485475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217524388552593098263922533 40785822853611205924485475)
                ·
                  refine ⟨61178734280416808886728213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40785822853611205924485475 61178734280416808886728213)
                  ·
                    refine ⟨2867753169394537916565385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61178734280416808886728213 2867753169394537916565385)
                    ·
                      refine ⟨2150814877045903437424039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2867753169394537916565385 2150814877045903437424039)
                      ·
                        rfl

theorem cell23_4188697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 6, 2].length) (baseStart_4188697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188697 prefixEnd_4188697 := by exact prefixLift 4188697
  have htrace : WordTrace (prefixWord ++ tailWord_4188697) baseStart_4188697 baseEnd_4188697 := by
    simpa [prefixWord, tailWord_4188697, baseEnd_4188697] using wordTrace_append hprefix tailTrace_4188697
  have hstable : (prefixWord ++ tailWord_4188697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188697).length < 2 ^ (prefixWord ++ tailWord_4188697).sum := by decide
  have hdescent : baseEnd_4188697 < baseStart_4188697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188714 : List Nat := [3, 1, 4, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_4188714 : Nat := 118140960795 + 4188714 * 2 ^ 59
def prefixEnd_4188714 : Nat := 4983230072969 + 3 ^ 40 * 4188714 * 2
def baseEnd_4188714 : Nat := 2150823606217029870911461

theorem tailTrace_4188714 : CollatzResearch.WordTrace tailWord_4188714 prefixEnd_4188714 2150823606217029870911461 := by
  unfold tailWord_4188714
  simp only [CollatzResearch.WordTrace]
  refine ⟨38193737636753007060591299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101849967031341352161576797 38193737636753007060591299)
  ·
    refine ⟨57290606455129510590886949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38193737636753007060591299 57290606455129510590886949)
    ·
      refine ⟨10741988710336783235791303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57290606455129510590886949 10741988710336783235791303)
      ·
        refine ⟨16112983065505174853686955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10741988710336783235791303 16112983065505174853686955)
        ·
          refine ⟨24169474598257762280530433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16112983065505174853686955 24169474598257762280530433)
          ·
            refine ⟨18127105948693321710397825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24169474598257762280530433 18127105948693321710397825)
            ·
              refine ⟨13595329461519991282798369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18127105948693321710397825 13595329461519991282798369)
              ·
                refine ⟨10196497096139993462098777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13595329461519991282798369 10196497096139993462098777)
                ·
                  refine ⟨7647372822104995096574083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10196497096139993462098777 7647372822104995096574083)
                  ·
                    refine ⟨11471059233157492644861125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7647372822104995096574083 11471059233157492644861125)
                    ·
                      refine ⟨2150823606217029870911461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11471059233157492644861125 2150823606217029870911461)
                      ·
                        rfl

theorem cell23_4188714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_4188714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188714 prefixEnd_4188714 := by exact prefixLift 4188714
  have htrace : WordTrace (prefixWord ++ tailWord_4188714) baseStart_4188714 baseEnd_4188714 := by
    simpa [prefixWord, tailWord_4188714, baseEnd_4188714] using wordTrace_append hprefix tailTrace_4188714
  have hstable : (prefixWord ++ tailWord_4188714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188714).length < 2 ^ (prefixWord ++ tailWord_4188714).sum := by decide
  have hdescent : baseEnd_4188714 < baseStart_4188714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188720 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 8]
def baseStart_4188720 : Nat := 118140960795 + 4188720 * 2 ^ 59
def prefixEnd_4188720 : Nat := 4983230072969 + 3 ^ 40 * 4188720 * 2
def baseEnd_4188720 : Nat := 238980743011217427492937

theorem tailTrace_4188720 : CollatzResearch.WordTrace tailWord_4188720 prefixEnd_4188720 238980743011217427492937 := by
  unfold tailWord_4188720
  simp only [CollatzResearch.WordTrace]
  refine ⟨76387584692495145633541807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101850112923326860844722409 76387584692495145633541807)
  ·
    refine ⟨114581377038742718450312711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76387584692495145633541807 114581377038742718450312711)
    ·
      refine ⟨171872065558114077675469067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114581377038742718450312711 171872065558114077675469067)
      ·
        refine ⟨257808098337171116513203601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171872065558114077675469067 257808098337171116513203601)
        ·
          refine ⟨193356073752878337384902701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257808098337171116513203601 193356073752878337384902701)
          ·
            refine ⟨72508527657329376519338513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193356073752878337384902701 72508527657329376519338513)
            ·
              refine ⟨54381395742997032389503885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72508527657329376519338513 54381395742997032389503885)
              ·
                refine ⟨20393023403623887146063957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54381395742997032389503885 20393023403623887146063957)
                ·
                  refine ⟨238980743011217427492937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20393023403623887146063957 238980743011217427492937)
                  ·
                    rfl

theorem cell23_4188720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 8].length) (baseStart_4188720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188720 prefixEnd_4188720 := by exact prefixLift 4188720
  have htrace : WordTrace (prefixWord ++ tailWord_4188720) baseStart_4188720 baseEnd_4188720 := by
    simpa [prefixWord, tailWord_4188720, baseEnd_4188720] using wordTrace_append hprefix tailTrace_4188720
  have hstable : (prefixWord ++ tailWord_4188720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188720).length < 2 ^ (prefixWord ++ tailWord_4188720).sum := by decide
  have hdescent : baseEnd_4188720 < baseStart_4188720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188781 : List Nat := [1, 5, 1, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_4188781 : Nat := 118140960795 + 4188781 * 2 ^ 59
def prefixEnd_4188781 : Nat := 4983230072969 + 3 ^ 40 * 4188781 * 2
def baseEnd_4188781 : Nat := 2150858009420881108773653

theorem tailTrace_4188781 : CollatzResearch.WordTrace tailWord_4188781 prefixEnd_4188781 2150858009420881108773653 := by
  unfold tailWord_4188781
  simp only [CollatzResearch.WordTrace]
  refine ⟨152777394237769298685054197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101851596158512865790036131 152777394237769298685054197)
  ·
    refine ⟨14322880709790871751723831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152777394237769298685054197 14322880709790871751723831)
    ·
      refine ⟨21484321064686307627585747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14322880709790871751723831 21484321064686307627585747)
      ·
        refine ⟨32226481597029461441378621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21484321064686307627585747 32226481597029461441378621)
        ·
          refine ⟨12084930598886048040516983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32226481597029461441378621 12084930598886048040516983)
          ·
            refine ⟨18127395898329072060775475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12084930598886048040516983 18127395898329072060775475)
            ·
              refine ⟨27191093847493608091163213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18127395898329072060775475 27191093847493608091163213)
              ·
                refine ⟨10196660192810103034186205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27191093847493608091163213 10196660192810103034186205)
                ·
                  refine ⟨3823747572303788637819827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10196660192810103034186205 3823747572303788637819827)
                  ·
                    refine ⟨5735621358455682956729741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3823747572303788637819827 5735621358455682956729741)
                    ·
                      refine ⟨2150858009420881108773653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5735621358455682956729741 2150858009420881108773653)
                      ·
                        rfl

theorem cell23_4188781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_4188781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188781 prefixEnd_4188781 := by exact prefixLift 4188781
  have htrace : WordTrace (prefixWord ++ tailWord_4188781) baseStart_4188781 baseEnd_4188781 := by
    simpa [prefixWord, tailWord_4188781, baseEnd_4188781] using wordTrace_append hprefix tailTrace_4188781
  have hstable : (prefixWord ++ tailWord_4188781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188781).length < 2 ^ (prefixWord ++ tailWord_4188781).sum := by decide
  have hdescent : baseEnd_4188781 < baseStart_4188781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188787 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 4]
def baseStart_4188787 : Nat := 118140960795 + 4188787 * 2 ^ 59
def prefixEnd_4188787 : Nat := 4983230072969 + 3 ^ 40 * 4188787 * 2
def baseEnd_4188787 : Nat := 2150861090304808085298625

theorem tailTrace_4188787 : CollatzResearch.WordTrace tailWord_4188787 prefixEnd_4188787 2150861090304808085298625 := by
  unfold tailWord_4188787
  simp only [CollatzResearch.WordTrace]
  refine ⟨152777613075747561709772615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101851742050498374473181743 152777613075747561709772615)
  ·
    refine ⟨229166419613621342564658923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152777613075747561709772615 229166419613621342564658923)
    ·
      refine ⟨343749629420432013846988385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229166419613621342564658923 343749629420432013846988385)
      ·
        refine ⟨257812222065324010385241289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343749629420432013846988385 257812222065324010385241289)
        ·
          refine ⟨193359166548993007788930967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257812222065324010385241289 193359166548993007788930967)
          ·
            refine ⟨290038749823489511683396451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193359166548993007788930967 290038749823489511683396451)
            ·
              refine ⟨435058124735234267525094677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290038749823489511683396451 435058124735234267525094677)
              ·
                refine ⟨20393349596964106290238813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 435058124735234267525094677 20393349596964106290238813)
                ·
                  refine ⟨7647506098861539858839555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20393349596964106290238813 7647506098861539858839555)
                  ·
                    refine ⟨11471259148292309788259333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7647506098861539858839555 11471259148292309788259333)
                    ·
                      refine ⟨2150861090304808085298625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11471259148292309788259333 2150861090304808085298625)
                      ·
                        rfl

theorem cell23_4188787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 4].length) (baseStart_4188787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188787 prefixEnd_4188787 := by exact prefixLift 4188787
  have htrace : WordTrace (prefixWord ++ tailWord_4188787) baseStart_4188787 baseEnd_4188787 := by
    simpa [prefixWord, tailWord_4188787, baseEnd_4188787] using wordTrace_append hprefix tailTrace_4188787
  have hstable : (prefixWord ++ tailWord_4188787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188787).length < 2 ^ (prefixWord ++ tailWord_4188787).sum := by decide
  have hdescent : baseEnd_4188787 < baseStart_4188787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188807 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_4188807 : Nat := 118140960795 + 4188807 * 2 ^ 59
def prefixEnd_4188807 : Nat := 4983230072969 + 3 ^ 40 * 4188807 * 2
def baseEnd_4188807 : Nat := 2150871359917898007048533

theorem tailTrace_4188807 : CollatzResearch.WordTrace tailWord_4188807 prefixEnd_4188807 2150871359917898007048533 := by
  unfold tailWord_4188807
  simp only [CollatzResearch.WordTrace]
  refine ⟨152778342535675105125500675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101852228357116736750333783 152778342535675105125500675)
  ·
    refine ⟨229167513803512657688251013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152778342535675105125500675 229167513803512657688251013)
    ·
      refine ⟨42968908838158623316547065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229167513803512657688251013 42968908838158623316547065)
      ·
        refine ⟨32226681628618967487410299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42968908838158623316547065 32226681628618967487410299)
        ·
          refine ⟨48340022442928451231115449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32226681628618967487410299 48340022442928451231115449)
          ·
            refine ⟨36255016832196338423336587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48340022442928451231115449 36255016832196338423336587)
            ·
              refine ⟨54382525248294507635004881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36255016832196338423336587 54382525248294507635004881)
              ·
                refine ⟨40786893936220880726253661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54382525248294507635004881 40786893936220880726253661)
                ·
                  refine ⟨15295085226082830272345123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40786893936220880726253661 15295085226082830272345123)
                  ·
                    refine ⟨22942627839124245408517685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15295085226082830272345123 22942627839124245408517685)
                    ·
                      refine ⟨2150871359917898007048533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22942627839124245408517685 2150871359917898007048533)
                      ·
                        rfl

theorem cell23_4188807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_4188807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188807 prefixEnd_4188807 := by exact prefixLift 4188807
  have htrace : WordTrace (prefixWord ++ tailWord_4188807) baseStart_4188807 baseEnd_4188807 := by
    simpa [prefixWord, tailWord_4188807, baseEnd_4188807] using wordTrace_append hprefix tailTrace_4188807
  have hstable : (prefixWord ++ tailWord_4188807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188807).length < 2 ^ (prefixWord ++ tailWord_4188807).sum := by decide
  have hdescent : baseEnd_4188807 < baseStart_4188807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188814 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 6, 4]
def baseStart_4188814 : Nat := 118140960795 + 4188814 * 2 ^ 59
def prefixEnd_4188814 : Nat := 4983230072969 + 3 ^ 40 * 4188814 * 2
def baseEnd_4188814 : Nat := 716958318094159826553667

theorem tailTrace_4188814 : CollatzResearch.WordTrace tailWord_4188814 prefixEnd_4188814 716958318094159826553667 := by
  unfold tailWord_4188814
  simp only [CollatzResearch.WordTrace]
  refine ⟨19097324730831218165125687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101852398564433163547336997 19097324730831218165125687)
  ·
    refine ⟨28645987096246827247688531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19097324730831218165125687 28645987096246827247688531)
    ·
      refine ⟨42968980644370240871532797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28645987096246827247688531 42968980644370240871532797)
      ·
        refine ⟨16113367741638840326824799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42968980644370240871532797 16113367741638840326824799)
        ·
          refine ⟨24170051612458260490237199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16113367741638840326824799 24170051612458260490237199)
          ·
            refine ⟨36255077418687390735355799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24170051612458260490237199 36255077418687390735355799)
            ·
              refine ⟨54382616128031086103033699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36255077418687390735355799 54382616128031086103033699)
              ·
                refine ⟨81573924192046629154550549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54382616128031086103033699 81573924192046629154550549)
                ·
                  refine ⟨3823777696502185741619557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81573924192046629154550549 3823777696502185741619557)
                  ·
                    refine ⟨716958318094159826553667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3823777696502185741619557 716958318094159826553667)
                    ·
                      rfl

theorem cell23_4188814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_4188814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188814 prefixEnd_4188814 := by exact prefixLift 4188814
  have htrace : WordTrace (prefixWord ++ tailWord_4188814) baseStart_4188814 baseEnd_4188814 := by
    simpa [prefixWord, tailWord_4188814, baseEnd_4188814] using wordTrace_append hprefix tailTrace_4188814
  have hstable : (prefixWord ++ tailWord_4188814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188814).length < 2 ^ (prefixWord ++ tailWord_4188814).sum := by decide
  have hdescent : baseEnd_4188814 < baseStart_4188814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188824 : List Nat := [2, 1, 2, 4, 1, 1, 4, 1, 1, 1, 5]
def baseStart_4188824 : Nat := 118140960795 + 4188824 * 2 ^ 59
def prefixEnd_4188824 : Nat := 4983230072969 + 3 ^ 40 * 4188824 * 2
def baseEnd_4188824 : Nat := 2150880089089024440535955

theorem tailTrace_4188824 : CollatzResearch.WordTrace tailWord_4188824 prefixEnd_4188824 2150880089089024440535955 := by
  unfold tailWord_4188824
  simp only [CollatzResearch.WordTrace]
  refine ⟨76389481288306758514434763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101852641717742344685913017 76389481288306758514434763)
  ·
    refine ⟨114584221932460137771652145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76389481288306758514434763 114584221932460137771652145)
    ·
      refine ⟨85938166449345103328739109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114584221932460137771652145 85938166449345103328739109)
      ·
        refine ⟨16113406209252206874138583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85938166449345103328739109 16113406209252206874138583)
        ·
          refine ⟨24170109313878310311207875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16113406209252206874138583 24170109313878310311207875)
          ·
            refine ⟨36255163970817465466811813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24170109313878310311207875 36255163970817465466811813)
            ·
              refine ⟨6797843244528274775027215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36255163970817465466811813 6797843244528274775027215)
              ·
                refine ⟨10196764866792412162540823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6797843244528274775027215 10196764866792412162540823)
                ·
                  refine ⟨15295147300188618243811235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10196764866792412162540823 15295147300188618243811235)
                  ·
                    refine ⟨22942720950282927365716853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15295147300188618243811235 22942720950282927365716853)
                    ·
                      refine ⟨2150880089089024440535955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22942720950282927365716853 2150880089089024440535955)
                      ·
                        rfl

theorem cell23_4188824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_4188824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188824 prefixEnd_4188824 := by exact prefixLift 4188824
  have htrace : WordTrace (prefixWord ++ tailWord_4188824) baseStart_4188824 baseEnd_4188824 := by
    simpa [prefixWord, tailWord_4188824, baseEnd_4188824] using wordTrace_append hprefix tailTrace_4188824
  have hstable : (prefixWord ++ tailWord_4188824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188824).length < 2 ^ (prefixWord ++ tailWord_4188824).sum := by decide
  have hdescent : baseEnd_4188824 < baseStart_4188824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188888 : List Nat := [2, 1, 2, 2, 3, 3, 2, 2, 2, 1, 3]
def baseStart_4188888 : Nat := 118140960795 + 4188888 * 2 ^ 59
def prefixEnd_4188888 : Nat := 4983230072969 + 3 ^ 40 * 4188888 * 2
def baseEnd_4188888 : Nat := 2150912951850912190135661

theorem tailTrace_4188888 : CollatzResearch.WordTrace tailWord_4188888 prefixEnd_4188888 2150912951850912190135661 := by
  unfold tailWord_4188888
  simp only [CollatzResearch.WordTrace]
  refine ⟨76390648424190827979599659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101854197898921103972799545 76390648424190827979599659)
  ·
    refine ⟨114585972636286241969399489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76390648424190827979599659 114585972636286241969399489)
    ·
      refine ⟨85939479477214681477049617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114585972636286241969399489 85939479477214681477049617)
      ·
        refine ⟨64454609607911011107787213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85939479477214681477049617 64454609607911011107787213)
        ·
          refine ⟨24170478602966629165420205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64454609607911011107787213 24170478602966629165420205)
          ·
            refine ⟨9063929476112485937032577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24170478602966629165420205 9063929476112485937032577)
            ·
              refine ⟨6797947107084364452774433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9063929476112485937032577 6797947107084364452774433)
              ·
                refine ⟨5098460330313273339580825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6797947107084364452774433 5098460330313273339580825)
                ·
                  refine ⟨3823845247734955004685619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5098460330313273339580825 3823845247734955004685619)
                  ·
                    refine ⟨5735767871602432507028429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3823845247734955004685619 5735767871602432507028429)
                    ·
                      refine ⟨2150912951850912190135661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5735767871602432507028429 2150912951850912190135661)
                      ·
                        rfl

theorem cell23_4188888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_4188888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188888 prefixEnd_4188888 := by exact prefixLift 4188888
  have htrace : WordTrace (prefixWord ++ tailWord_4188888) baseStart_4188888 baseEnd_4188888 := by
    simpa [prefixWord, tailWord_4188888, baseEnd_4188888] using wordTrace_append hprefix tailTrace_4188888
  have hstable : (prefixWord ++ tailWord_4188888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188888).length < 2 ^ (prefixWord ++ tailWord_4188888).sum := by decide
  have hdescent : baseEnd_4188888 < baseStart_4188888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188911 : List Nat := [1, 1, 2, 1, 5, 2, 1, 3, 1, 4, 2]
def baseStart_4188911 : Nat := 118140960795 + 4188911 * 2 ^ 59
def prefixEnd_4188911 : Nat := 4983230072969 + 3 ^ 40 * 4188911 * 2
def baseEnd_4188911 : Nat := 2150924761905965600148055

theorem tailTrace_4188911 : CollatzResearch.WordTrace tailWord_4188911 prefixEnd_4188911 2150924761905965600148055 := by
  unfold tailWord_4188911
  simp only [CollatzResearch.WordTrace]
  refine ⟨152782135727298330887286587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101854757151532220591524391 152782135727298330887286587)
  ·
    refine ⟨229173203590947496330929881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152782135727298330887286587 229173203590947496330929881)
    ·
      refine ⟨171879902693210622248197411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229173203590947496330929881 171879902693210622248197411)
      ·
        refine ⟨257819854039815933372296117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171879902693210622248197411 257819854039815933372296117)
        ·
          refine ⟨24170611316232743753652761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257819854039815933372296117 24170611316232743753652761)
          ·
            refine ⟨18127958487174557815239571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24170611316232743753652761 18127958487174557815239571)
            ·
              refine ⟨27191937730761836722859357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18127958487174557815239571 27191937730761836722859357)
              ·
                refine ⟨10196976649035688771072259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27191937730761836722859357 10196976649035688771072259)
                ·
                  refine ⟨15295464973553533156608389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10196976649035688771072259 15295464973553533156608389)
                  ·
                    refine ⟨2867899682541287466864073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15295464973553533156608389 2867899682541287466864073)
                    ·
                      refine ⟨2150924761905965600148055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2867899682541287466864073 2150924761905965600148055)
                      ·
                        rfl

theorem cell23_4188911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 4, 2].length) (baseStart_4188911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188911 prefixEnd_4188911 := by exact prefixLift 4188911
  have htrace : WordTrace (prefixWord ++ tailWord_4188911) baseStart_4188911 baseEnd_4188911 := by
    simpa [prefixWord, tailWord_4188911, baseEnd_4188911] using wordTrace_append hprefix tailTrace_4188911
  have hstable : (prefixWord ++ tailWord_4188911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188911).length < 2 ^ (prefixWord ++ tailWord_4188911).sum := by decide
  have hdescent : baseEnd_4188911 < baseStart_4188911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188927 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 7]
def baseStart_4188927 : Nat := 118140960795 + 4188927 * 2 ^ 59
def prefixEnd_4188927 : Nat := 4983230072969 + 3 ^ 40 * 4188927 * 2
def baseEnd_4188927 : Nat := 2150932977596437537547981

theorem tailTrace_4188927 : CollatzResearch.WordTrace tailWord_4188927 prefixEnd_4188927 2150932977596437537547981 := by
  unfold tailWord_4188927
  simp only [CollatzResearch.WordTrace]
  refine ⟨152782719295240365619869035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101855146196826910413246023 152782719295240365619869035)
  ·
    refine ⟨229174078942860548429803553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152782719295240365619869035 229174078942860548429803553)
    ·
      refine ⟨171880559207145411322352665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229174078942860548429803553 171880559207145411322352665)
      ·
        refine ⟨128910419405359058491764499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171880559207145411322352665 128910419405359058491764499)
        ·
          refine ⟨193365629108038587737646749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128910419405359058491764499 193365629108038587737646749)
          ·
            refine ⟨72512110915514470401617531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193365629108038587737646749 72512110915514470401617531)
            ·
              refine ⟨108768166373271705602426297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72512110915514470401617531 108768166373271705602426297)
              ·
                refine ⟨81576124779953779201819723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108768166373271705602426297 81576124779953779201819723)
                ·
                  refine ⟨122364187169930668802729585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81576124779953779201819723 122364187169930668802729585)
                  ·
                    refine ⟨91773140377448001602047189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122364187169930668802729585 91773140377448001602047189)
                    ·
                      refine ⟨2150932977596437537547981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91773140377448001602047189 2150932977596437537547981)
                      ·
                        rfl

theorem cell23_4188927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_4188927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188927 prefixEnd_4188927 := by exact prefixLift 4188927
  have htrace : WordTrace (prefixWord ++ tailWord_4188927) baseStart_4188927 baseEnd_4188927 := by
    simpa [prefixWord, tailWord_4188927, baseEnd_4188927] using wordTrace_append hprefix tailTrace_4188927
  have hstable : (prefixWord ++ tailWord_4188927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188927).length < 2 ^ (prefixWord ++ tailWord_4188927).sum := by decide
  have hdescent : baseEnd_4188927 < baseStart_4188927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188951 : List Nat := [1, 1, 3, 4, 3, 1, 2, 1, 7]
def baseStart_4188951 : Nat := 118140960795 + 4188951 * 2 ^ 59
def prefixEnd_4188951 : Nat := 4983230072969 + 3 ^ 40 * 4188951 * 2
def baseEnd_4188951 : Nat := 238993922348016160405319

theorem tailTrace_4188951 : CollatzResearch.WordTrace tailWord_4188951 prefixEnd_4188951 238993922348016160405319 := by
  unfold tailWord_4188951
  simp only [CollatzResearch.WordTrace]
  refine ⟨152783594647153417718742707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101855729764768945145828471 152783594647153417718742707)
  ·
    refine ⟨229175391970730126578114061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152783594647153417718742707 229175391970730126578114061)
    ·
      refine ⟨85940771989023797466792773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229175391970730126578114061 85940771989023797466792773)
      ·
        refine ⟨16113894747941962025023645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85940771989023797466792773 16113894747941962025023645)
        ·
          refine ⟨6042710530478235759383867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16113894747941962025023645 6042710530478235759383867)
          ·
            refine ⟨9064065795717353639075801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6042710530478235759383867 9064065795717353639075801)
            ·
              refine ⟨6798049346788015229306851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9064065795717353639075801 6798049346788015229306851)
              ·
                refine ⟨10197074020182022843960277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6798049346788015229306851 10197074020182022843960277)
                ·
                  refine ⟨238993922348016160405319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10197074020182022843960277 238993922348016160405319)
                  ·
                    rfl

theorem cell23_4188951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 7].length) (baseStart_4188951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188951 prefixEnd_4188951 := by exact prefixLift 4188951
  have htrace : WordTrace (prefixWord ++ tailWord_4188951) baseStart_4188951 baseEnd_4188951 := by
    simpa [prefixWord, tailWord_4188951, baseEnd_4188951] using wordTrace_append hprefix tailTrace_4188951
  have hstable : (prefixWord ++ tailWord_4188951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188951).length < 2 ^ (prefixWord ++ tailWord_4188951).sum := by decide
  have hdescent : baseEnd_4188951 < baseStart_4188951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188962 : List Nat := [3, 3, 1, 1, 2, 3, 3, 1, 2, 2, 2]
def baseStart_4188962 : Nat := 118140960795 + 4188962 * 2 ^ 59
def prefixEnd_4188962 : Nat := 4983230072969 + 3 ^ 40 * 4188962 * 2
def baseEnd_4188962 : Nat := 2150950949419344900610321

theorem tailTrace_4188962 : CollatzResearch.WordTrace tailWord_4188962 prefixEnd_4188962 2150950949419344900610321 := by
  unfold tailWord_4188962
  simp only [CollatzResearch.WordTrace]
  refine ⟨38195998962528391649348285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101855997233409044398262093 38195998962528391649348285)
  ·
    refine ⟨14323499610948146868505607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38195998962528391649348285 14323499610948146868505607)
    ·
      refine ⟨21485249416422220302758411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14323499610948146868505607 21485249416422220302758411)
      ·
        refine ⟨32227874124633330454137617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21485249416422220302758411 32227874124633330454137617)
        ·
          refine ⟨24170905593474997840603213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32227874124633330454137617 24170905593474997840603213)
          ·
            refine ⟨9064089597553124190226205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24170905593474997840603213 9064089597553124190226205)
            ·
              refine ⟨3399033599082421571334827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9064089597553124190226205 3399033599082421571334827)
              ·
                refine ⟨5098550398623632357002241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3399033599082421571334827 5098550398623632357002241)
                ·
                  refine ⟨3823912798967724267751681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5098550398623632357002241 3823912798967724267751681)
                  ·
                    refine ⟨2867934599225793200813761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3823912798967724267751681 2867934599225793200813761)
                    ·
                      refine ⟨2150950949419344900610321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2867934599225793200813761 2150950949419344900610321)
                      ·
                        rfl

theorem cell23_4188962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_4188962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188962 prefixEnd_4188962 := by exact prefixLift 4188962
  have htrace : WordTrace (prefixWord ++ tailWord_4188962) baseStart_4188962 baseEnd_4188962 := by
    simpa [prefixWord, tailWord_4188962, baseEnd_4188962] using wordTrace_append hprefix tailTrace_4188962
  have hstable : (prefixWord ++ tailWord_4188962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188962).length < 2 ^ (prefixWord ++ tailWord_4188962).sum := by decide
  have hdescent : baseEnd_4188962 < baseStart_4188962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188984 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 1, 3, 4]
def baseStart_4188984 : Nat := 118140960795 + 4188984 * 2 ^ 59
def prefixEnd_4188984 : Nat := 4983230072969 + 3 ^ 40 * 4188984 * 2
def baseEnd_4188984 : Nat := 2150962245993743814535219

theorem tailTrace_4188984 : CollatzResearch.WordTrace tailWord_4188984 prefixEnd_4188984 2150962245993743814535219 := by
  unfold tailWord_4188984
  simp only [CollatzResearch.WordTrace]
  refine ⟨76392399128016932177347003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101856532170689242903129337 76392399128016932177347003)
  ·
    refine ⟨114588598692025398266020505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76392399128016932177347003 114588598692025398266020505)
    ·
      refine ⟨85941449019019048699515379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114588598692025398266020505 85941449019019048699515379)
      ·
        refine ⟨128912173528528573049273069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85941449019019048699515379 128912173528528573049273069)
        ·
          refine ⟨48342065073198214893477401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128912173528528573049273069 48342065073198214893477401)
          ·
            refine ⟨36256548804898661170108051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48342065073198214893477401 36256548804898661170108051)
            ·
              refine ⟨54384823207347991755162077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36256548804898661170108051 54384823207347991755162077)
              ·
                refine ⟨20394308702755496908185779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54384823207347991755162077 20394308702755496908185779)
                ·
                  refine ⟨30591463054133245362278669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20394308702755496908185779 30591463054133245362278669)
                  ·
                    refine ⟨11471798645299967010854501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30591463054133245362278669 11471798645299967010854501)
                    ·
                      refine ⟨2150962245993743814535219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11471798645299967010854501 2150962245993743814535219)
                      ·
                        rfl

theorem cell23_4188984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_4188984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4188984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4188984 prefixEnd_4188984 := by exact prefixLift 4188984
  have htrace : WordTrace (prefixWord ++ tailWord_4188984) baseStart_4188984 baseEnd_4188984 := by
    simpa [prefixWord, tailWord_4188984, baseEnd_4188984] using wordTrace_append hprefix tailTrace_4188984
  have hstable : (prefixWord ++ tailWord_4188984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188984).length < 2 ^ (prefixWord ++ tailWord_4188984).sum := by decide
  have hdescent : baseEnd_4188984 < baseStart_4188984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189001 : List Nat := [1, 2, 1, 1, 2, 6, 1, 2, 2, 1, 4]
def baseStart_4189001 : Nat := 118140960795 + 4189001 * 2 ^ 59
def prefixEnd_4189001 : Nat := 4983230072969 + 3 ^ 40 * 4189001 * 2
def baseEnd_4189001 : Nat := 2150970975164870248022641

theorem tailTrace_4189001 : CollatzResearch.WordTrace tailWord_4189001 prefixEnd_4189001 2150970975164870248022641 := by
  unfold tailWord_4189001
  simp only [CollatzResearch.WordTrace]
  refine ⟨152785418296972276258062857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101856945531314850838708571 152785418296972276258062857)
  ·
    refine ⟨114589063722729207193547143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152785418296972276258062857 114589063722729207193547143)
    ·
      refine ⟨171883595584093810790320715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114589063722729207193547143 171883595584093810790320715)
      ·
        refine ⟨257825393376140716185481073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171883595584093810790320715 257825393376140716185481073)
        ·
          refine ⟨193369045032105537139110805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257825393376140716185481073 193369045032105537139110805)
          ·
            refine ⟨9064173985879947053395819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 193369045032105537139110805 9064173985879947053395819)
            ·
              refine ⟨13596260978819920580093729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9064173985879947053395819 13596260978819920580093729)
              ·
                refine ⟨10197195734114940435070297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13596260978819920580093729 10197195734114940435070297)
                ·
                  refine ⟨7647896800586205326302723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10197195734114940435070297 7647896800586205326302723)
                  ·
                    refine ⟨11471845200879307989454085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7647896800586205326302723 11471845200879307989454085)
                    ·
                      refine ⟨2150970975164870248022641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11471845200879307989454085 2150970975164870248022641)
                      ·
                        rfl

theorem cell23_4189001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 1, 4].length) (baseStart_4189001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189001 prefixEnd_4189001 := by exact prefixLift 4189001
  have htrace : WordTrace (prefixWord ++ tailWord_4189001) baseStart_4189001 baseEnd_4189001 := by
    simpa [prefixWord, tailWord_4189001, baseEnd_4189001] using wordTrace_append hprefix tailTrace_4189001
  have hstable : (prefixWord ++ tailWord_4189001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189001).length < 2 ^ (prefixWord ++ tailWord_4189001).sum := by decide
  have hdescent : baseEnd_4189001 < baseStart_4189001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189091 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 4]
def baseStart_4189091 : Nat := 118140960795 + 4189091 * 2 ^ 59
def prefixEnd_4189091 : Nat := 4983230072969 + 3 ^ 40 * 4189091 * 2
def baseEnd_4189091 : Nat := 2151017188423774895897227

theorem tailTrace_4189091 : CollatzResearch.WordTrace tailWord_4189091 prefixEnd_4189091 2151017188423774895897227 := by
  unfold tailWord_4189091
  simp only [CollatzResearch.WordTrace]
  refine ⟨152788700866646221628839127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101859133911097481085892751 152788700866646221628839127)
  ·
    refine ⟨229183051299969332443258691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152788700866646221628839127 229183051299969332443258691)
    ·
      refine ⟨343774576949953998664888037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229183051299969332443258691 343774576949953998664888037)
      ·
        refine ⟨64457733178116374749666507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343774576949953998664888037 64457733178116374749666507)
        ·
          refine ⟨96686599767174562124499761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64457733178116374749666507 96686599767174562124499761)
          ·
            refine ⟨72514949825380921593374821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96686599767174562124499761 72514949825380921593374821)
            ·
              refine ⟨13596553092258922798757779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72514949825380921593374821 13596553092258922798757779)
              ·
                refine ⟨20394829638388384198136669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13596553092258922798757779 20394829638388384198136669)
                ·
                  refine ⟨7648061114395644074301251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20394829638388384198136669 7648061114395644074301251)
                  ·
                    refine ⟨11472091671593466111451877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7648061114395644074301251 11472091671593466111451877)
                    ·
                      refine ⟨2151017188423774895897227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11472091671593466111451877 2151017188423774895897227)
                      ·
                        rfl

theorem cell23_4189091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_4189091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189091 prefixEnd_4189091 := by exact prefixLift 4189091
  have htrace : WordTrace (prefixWord ++ tailWord_4189091) baseStart_4189091 baseEnd_4189091 := by
    simpa [prefixWord, tailWord_4189091, baseEnd_4189091] using wordTrace_append hprefix tailTrace_4189091
  have hstable : (prefixWord ++ tailWord_4189091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189091).length < 2 ^ (prefixWord ++ tailWord_4189091).sum := by decide
  have hdescent : baseEnd_4189091 < baseStart_4189091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189095 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_4189095 : Nat := 118140960795 + 4189095 * 2 ^ 59
def prefixEnd_4189095 : Nat := 4983230072969 + 3 ^ 40 * 4189095 * 2
def baseEnd_4189095 : Nat := 2151019242346392880247209

theorem tailTrace_4189095 : CollatzResearch.WordTrace tailWord_4189095 prefixEnd_4189095 2151019242346392880247209 := by
  unfold tailWord_4189095
  simp only [CollatzResearch.WordTrace]
  refine ⟨152788846758631730311984739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101859231172421153541323159 152788846758631730311984739)
  ·
    refine ⟨229183270137947595467977109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152788846758631730311984739 229183270137947595467977109)
    ·
      refine ⟨10742965787716293537561427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 229183270137947595467977109 10742965787716293537561427)
      ·
        refine ⟨16114448681574440306342141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10742965787716293537561427 16114448681574440306342141)
        ·
          refine ⟨6042918255590415114878303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16114448681574440306342141 6042918255590415114878303)
          ·
            refine ⟨9064377383385622672317455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6042918255590415114878303 9064377383385622672317455)
            ·
              refine ⟨13596566075078434008476183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9064377383385622672317455 13596566075078434008476183)
              ·
                refine ⟨20394849112617651012714275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13596566075078434008476183 20394849112617651012714275)
                ·
                  refine ⟨30592273668926476519071413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20394849112617651012714275 30592273668926476519071413)
                  ·
                    refine ⟨2868025656461857173662945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30592273668926476519071413 2868025656461857173662945)
                    ·
                      refine ⟨2151019242346392880247209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2868025656461857173662945 2151019242346392880247209)
                      ·
                        rfl

theorem cell23_4189095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_4189095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189095 prefixEnd_4189095 := by exact prefixLift 4189095
  have htrace : WordTrace (prefixWord ++ tailWord_4189095) baseStart_4189095 baseEnd_4189095 := by
    simpa [prefixWord, tailWord_4189095, baseEnd_4189095] using wordTrace_append hprefix tailTrace_4189095
  have hstable : (prefixWord ++ tailWord_4189095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189095).length < 2 ^ (prefixWord ++ tailWord_4189095).sum := by decide
  have hdescent : baseEnd_4189095 < baseStart_4189095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189114 : List Nat := [3, 1, 1, 1, 2, 1, 14]
def baseStart_4189114 : Nat := 118140960795 + 4189114 * 2 ^ 59
def prefixEnd_4189114 : Nat := 4983230072969 + 3 ^ 40 * 4189114 * 2
def baseEnd_4189114 : Nat := 26555913561467016122341

theorem tailTrace_4189114 : CollatzResearch.WordTrace tailWord_4189114 prefixEnd_4189114 26555913561467016122341 := by
  unfold tailWord_4189114
  simp only [CollatzResearch.WordTrace]
  refine ⟨38197384936390724139231599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101859693163708597704617597 38197384936390724139231599)
  ·
    refine ⟨57296077404586086208847399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38197384936390724139231599 57296077404586086208847399)
    ·
      refine ⟨85944116106879129313271099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57296077404586086208847399 85944116106879129313271099)
      ·
        refine ⟨128916174160318693969906649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85944116106879129313271099 128916174160318693969906649)
        ·
          refine ⟨96687130620239020477429987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128916174160318693969906649 96687130620239020477429987)
          ·
            refine ⟨145030695930358530716144981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96687130620239020477429987 145030695930358530716144981)
            ·
              refine ⟨26555913561467016122341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 145030695930358530716144981 26555913561467016122341)
              ·
                rfl

theorem cell23_4189114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 14].length) (baseStart_4189114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189114 prefixEnd_4189114 := by exact prefixLift 4189114
  have htrace : WordTrace (prefixWord ++ tailWord_4189114) baseStart_4189114 baseEnd_4189114 := by
    simpa [prefixWord, tailWord_4189114, baseEnd_4189114] using wordTrace_append hprefix tailTrace_4189114
  have hstable : (prefixWord ++ tailWord_4189114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189114).length < 2 ^ (prefixWord ++ tailWord_4189114).sum := by decide
  have hdescent : baseEnd_4189114 < baseStart_4189114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189118 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_4189118 : Nat := 118140960795 + 4189118 * 2 ^ 59
def prefixEnd_4189118 : Nat := 4983230072969 + 3 ^ 40 * 4189118 * 2
def baseEnd_4189118 : Nat := 717010350800482096753201

theorem tailTrace_4189118 : CollatzResearch.WordTrace tailWord_4189118 prefixEnd_4189118 717010350800482096753201 := by
  unfold tailWord_4189118
  simp only [CollatzResearch.WordTrace]
  refine ⟨19098710704693550655009001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101859790425032270160048005 19098710704693550655009001)
  ·
    refine ⟨14324033028520162991256751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19098710704693550655009001 14324033028520162991256751)
    ·
      refine ⟨21486049542780244486885127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14324033028520162991256751 21486049542780244486885127)
      ·
        refine ⟨32229074314170366730327691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21486049542780244486885127 32229074314170366730327691)
        ·
          refine ⟨48343611471255550095491537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32229074314170366730327691 48343611471255550095491537)
          ·
            refine ⟨36257708603441662571618653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48343611471255550095491537 36257708603441662571618653)
            ·
              refine ⟨13596640726290623464356995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36257708603441662571618653 13596640726290623464356995)
              ·
                refine ⟨20394961089435935196535493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13596640726290623464356995 20394961089435935196535493)
                ·
                  refine ⟨3824055204269237849350405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20394961089435935196535493 3824055204269237849350405)
                  ·
                    refine ⟨717010350800482096753201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3824055204269237849350405 717010350800482096753201)
                    ·
                      rfl

theorem cell23_4189118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_4189118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189118 prefixEnd_4189118 := by exact prefixLift 4189118
  have htrace : WordTrace (prefixWord ++ tailWord_4189118) baseStart_4189118 baseEnd_4189118 := by
    simpa [prefixWord, tailWord_4189118, baseEnd_4189118] using wordTrace_append hprefix tailTrace_4189118
  have hstable : (prefixWord ++ tailWord_4189118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189118).length < 2 ^ (prefixWord ++ tailWord_4189118).sum := by decide
  have hdescent : baseEnd_4189118 < baseStart_4189118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189126 : List Nat := [6, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_4189126 : Nat := 118140960795 + 4189126 * 2 ^ 59
def prefixEnd_4189126 : Nat := 4983230072969 + 3 ^ 40 * 4189126 * 2
def baseEnd_4189126 : Nat := 239003906694075806551063

theorem tailTrace_4189126 : CollatzResearch.WordTrace tailWord_4189126 prefixEnd_4189126 239003906694075806551063 := by
  unfold tailWord_4189126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4774686794422481956448851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101859984947679615070908821 4774686794422481956448851)
  ·
    refine ⟨7162030191633722934673277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4774686794422481956448851 7162030191633722934673277)
    ·
      refine ⟨2685761321862646100502479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7162030191633722934673277 2685761321862646100502479)
      ·
        refine ⟨4028641982793969150753719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2685761321862646100502479 4028641982793969150753719)
        ·
          refine ⟨6042962974190953726130579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4028641982793969150753719 6042962974190953726130579)
          ·
            refine ⟨9064444461286430589195869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6042962974190953726130579 9064444461286430589195869)
            ·
              refine ⟨3399166672982411470948451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9064444461286430589195869 3399166672982411470948451)
              ·
                refine ⟨5098750009473617206422677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3399166672982411470948451 5098750009473617206422677)
                ·
                  refine ⟨239003906694075806551063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5098750009473617206422677 239003906694075806551063)
                  ·
                    rfl

theorem cell23_4189126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_4189126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189126 prefixEnd_4189126 := by exact prefixLift 4189126
  have htrace : WordTrace (prefixWord ++ tailWord_4189126) baseStart_4189126 baseEnd_4189126 := by
    simpa [prefixWord, tailWord_4189126, baseEnd_4189126] using wordTrace_append hprefix tailTrace_4189126
  have hstable : (prefixWord ++ tailWord_4189126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189126).length < 2 ^ (prefixWord ++ tailWord_4189126).sum := by decide
  have hdescent : baseEnd_4189126 < baseStart_4189126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189128 : List Nat := [2, 1, 3, 1, 5, 1, 1, 2, 1, 1, 5]
def baseStart_4189128 : Nat := 118140960795 + 4189128 * 2 ^ 59
def prefixEnd_4189128 : Nat := 4983230072969 + 3 ^ 40 * 4189128 * 2
def baseEnd_4189128 : Nat := 2151036187207991251134557

theorem tailTrace_4189128 : CollatzResearch.WordTrace tailWord_4189128 prefixEnd_4189128 2151036187207991251134557 := by
  unfold tailWord_4189128
  simp only [CollatzResearch.WordTrace]
  refine ⟨76395025183756088473968019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101860033578341451298624025 76395025183756088473968019)
  ·
    refine ⟨114592537775634132710952029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76395025183756088473968019 114592537775634132710952029)
    ·
      refine ⟨42972201665862799766607011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114592537775634132710952029 42972201665862799766607011)
      ·
        refine ⟨64458302498794199649910517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42972201665862799766607011 64458302498794199649910517)
        ·
          refine ⟨6042965859261956217179111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64458302498794199649910517 6042965859261956217179111)
          ·
            refine ⟨9064448788892934325768667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6042965859261956217179111 9064448788892934325768667)
            ·
              refine ⟨13596673183339401488653001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9064448788892934325768667 13596673183339401488653001)
              ·
                refine ⟨10197504887504551116489751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13596673183339401488653001 10197504887504551116489751)
                ·
                  refine ⟨15296257331256826674734627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10197504887504551116489751 15296257331256826674734627)
                  ·
                    refine ⟨22944385996885240012101941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15296257331256826674734627 22944385996885240012101941)
                    ·
                      refine ⟨2151036187207991251134557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22944385996885240012101941 2151036187207991251134557)
                      ·
                        rfl

theorem cell23_4189128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_4189128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189128 prefixEnd_4189128 := by exact prefixLift 4189128
  have htrace : WordTrace (prefixWord ++ tailWord_4189128) baseStart_4189128 baseEnd_4189128 := by
    simpa [prefixWord, tailWord_4189128, baseEnd_4189128] using wordTrace_append hprefix tailTrace_4189128
  have hstable : (prefixWord ++ tailWord_4189128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189128).length < 2 ^ (prefixWord ++ tailWord_4189128).sum := by decide
  have hdescent : baseEnd_4189128 < baseStart_4189128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189135 : List Nat := [1, 1, 2, 1, 1, 7, 3, 1, 2, 4]
def baseStart_4189135 : Nat := 118140960795 + 4189135 * 2 ^ 59
def prefixEnd_4189135 : Nat := 4983230072969 + 3 ^ 40 * 4189135 * 2
def baseEnd_4189135 : Nat := 717013260524190907915675

theorem tailTrace_4189135 : CollatzResearch.WordTrace tailWord_4189135 prefixEnd_4189135 717013260524190907915675 := by
  unfold tailWord_4189135
  simp only [CollatzResearch.WordTrace]
  refine ⟨152790305678486817143440859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101860203785657878095627239 152790305678486817143440859)
  ·
    refine ⟨229185458517730225715161289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152790305678486817143440859 229185458517730225715161289)
    ·
      refine ⟨171889093888297669286370967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229185458517730225715161289 171889093888297669286370967)
      ·
        refine ⟨257833640832446503929556451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171889093888297669286370967 257833640832446503929556451)
        ·
          refine ⟨386750461248669755894334677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257833640832446503929556451 386750461248669755894334677)
          ·
            refine ⟨9064463935515697403773469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 386750461248669755894334677 9064463935515697403773469)
            ·
              refine ⟨3399173975818386526415051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9064463935515697403773469 3399173975818386526415051)
              ·
                refine ⟨5098760963727579789622577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3399173975818386526415051 5098760963727579789622577)
                ·
                  refine ⟨3824070722795684842216933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5098760963727579789622577 3824070722795684842216933)
                  ·
                    refine ⟨717013260524190907915675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3824070722795684842216933 717013260524190907915675)
                    ·
                      rfl

theorem cell23_4189135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 2, 4].length) (baseStart_4189135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189135 prefixEnd_4189135 := by exact prefixLift 4189135
  have htrace : WordTrace (prefixWord ++ tailWord_4189135) baseStart_4189135 baseEnd_4189135 := by
    simpa [prefixWord, tailWord_4189135, baseEnd_4189135] using wordTrace_append hprefix tailTrace_4189135
  have hstable : (prefixWord ++ tailWord_4189135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189135).length < 2 ^ (prefixWord ++ tailWord_4189135).sum := by decide
  have hdescent : baseEnd_4189135 < baseStart_4189135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189138 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_4189138 : Nat := 118140960795 + 4189138 * 2 ^ 59
def prefixEnd_4189138 : Nat := 4983230072969 + 3 ^ 40 * 4189138 * 2
def baseEnd_4189138 : Nat := 2151041322014536212009511

theorem tailTrace_4189138 : CollatzResearch.WordTrace tailWord_4189138 prefixEnd_4189138 2151041322014536212009511 := by
  unfold tailWord_4189138
  simp only [CollatzResearch.WordTrace]
  refine ⟨38197603774368987163950017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101860276731650632437200045 38197603774368987163950017)
  ·
    refine ⟨28648202830776740372962513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38197603774368987163950017 28648202830776740372962513)
    ·
      refine ⟨21486152123082555279721885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28648202830776740372962513 21486152123082555279721885)
      ·
        refine ⟨8057307046155958229895707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21486152123082555279721885 8057307046155958229895707)
        ·
          refine ⟨12085960569233937344843561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8057307046155958229895707 12085960569233937344843561)
          ·
            refine ⟨9064470426925453008632671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12085960569233937344843561 9064470426925453008632671)
            ·
              refine ⟨13596705640388179512949007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9064470426925453008632671 13596705640388179512949007)
              ·
                refine ⟨20395058460582269269423511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13596705640388179512949007 20395058460582269269423511)
                ·
                  refine ⟨30592587690873403904135267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20395058460582269269423511 30592587690873403904135267)
                  ·
                    refine ⟨45888881536310105856202901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30592587690873403904135267 45888881536310105856202901)
                    ·
                      refine ⟨2151041322014536212009511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45888881536310105856202901 2151041322014536212009511)
                      ·
                        rfl

theorem cell23_4189138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_4189138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189138 prefixEnd_4189138 := by exact prefixLift 4189138
  have htrace : WordTrace (prefixWord ++ tailWord_4189138) baseStart_4189138 baseEnd_4189138 := by
    simpa [prefixWord, tailWord_4189138, baseEnd_4189138] using wordTrace_append hprefix tailTrace_4189138
  have hstable : (prefixWord ++ tailWord_4189138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189138).length < 2 ^ (prefixWord ++ tailWord_4189138).sum := by decide
  have hdescent : baseEnd_4189138 < baseStart_4189138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189142 : List Nat := [5, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_4189142 : Nat := 118140960795 + 4189142 * 2 ^ 59
def prefixEnd_4189142 : Nat := 4983230072969 + 3 ^ 40 * 4189142 * 2
def baseEnd_4189142 : Nat := 2151043375937154196359493

theorem tailTrace_4189142 : CollatzResearch.WordTrace tailWord_4189142 prefixEnd_4189142 2151043375937154196359493 := by
  unfold tailWord_4189142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9549410061841341083684105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101860373992974304892630453 9549410061841341083684105)
  ·
    refine ⟨7162057546381005812763079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9549410061841341083684105 7162057546381005812763079)
    ·
      refine ⟨10743086319571508719144619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7162057546381005812763079 10743086319571508719144619)
      ·
        refine ⟨16114629479357263078716929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10743086319571508719144619 16114629479357263078716929)
        ·
          refine ⟨12085972109517947309037697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16114629479357263078716929 12085972109517947309037697)
          ·
            refine ⟨9064479082138460481778273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12085972109517947309037697 9064479082138460481778273)
            ·
              refine ⟨6798359311603845361333705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9064479082138460481778273 6798359311603845361333705)
              ·
                refine ⟨5098769483702884021000279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6798359311603845361333705 5098769483702884021000279)
                ·
                  refine ⟨7648154225554326031500419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098769483702884021000279 7648154225554326031500419)
                  ·
                    refine ⟨11472231338331489047250629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7648154225554326031500419 11472231338331489047250629)
                    ·
                      refine ⟨2151043375937154196359493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11472231338331489047250629 2151043375937154196359493)
                      ·
                        rfl

theorem cell23_4189142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_4189142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189142 prefixEnd_4189142 := by exact prefixLift 4189142
  have htrace : WordTrace (prefixWord ++ tailWord_4189142) baseStart_4189142 baseEnd_4189142 := by
    simpa [prefixWord, tailWord_4189142, baseEnd_4189142] using wordTrace_append hprefix tailTrace_4189142
  have hstable : (prefixWord ++ tailWord_4189142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189142).length < 2 ^ (prefixWord ++ tailWord_4189142).sum := by decide
  have hdescent : baseEnd_4189142 < baseStart_4189142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189145 : List Nat := [1, 2, 1, 2, 5, 2, 2, 2, 1, 2, 3]
def baseStart_4189145 : Nat := 118140960795 + 4189145 * 2 ^ 59
def prefixEnd_4189145 : Nat := 4983230072969 + 3 ^ 40 * 4189145 * 2
def baseEnd_4189145 : Nat := 2151044916379117684621979

theorem tailTrace_4189145 : CollatzResearch.WordTrace tailWord_4189145 prefixEnd_4189145 2151044916379117684621979 := by
  unfold tailWord_4189145
  simp only [CollatzResearch.WordTrace]
  refine ⟨152790670408450588851304889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101860446938967059234203259 152790670408450588851304889)
  ·
    refine ⟨114593002806337941638478667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152790670408450588851304889 114593002806337941638478667)
    ·
      refine ⟨171889504209506912457718001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114593002806337941638478667 171889504209506912457718001)
      ·
        refine ⟨128917128157130184343288501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171889504209506912457718001 128917128157130184343288501)
        ·
          refine ⟨12085980764730954782183297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128917128157130184343288501 12085980764730954782183297)
          ·
            refine ⟨9064485573548216086637473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12085980764730954782183297 9064485573548216086637473)
            ·
              refine ⟨6798364180161162064978105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9064485573548216086637473 6798364180161162064978105)
              ·
                refine ⟨5098773135120871548733579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6798364180161162064978105 5098773135120871548733579)
                ·
                  refine ⟨7648159702681307323100369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098773135120871548733579 7648159702681307323100369)
                  ·
                    refine ⟨5736119777010980492325277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7648159702681307323100369 5736119777010980492325277)
                    ·
                      refine ⟨2151044916379117684621979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5736119777010980492325277 2151044916379117684621979)
                      ·
                        rfl

theorem cell23_4189145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 2, 3].length) (baseStart_4189145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189145 prefixEnd_4189145 := by exact prefixLift 4189145
  have htrace : WordTrace (prefixWord ++ tailWord_4189145) baseStart_4189145 baseEnd_4189145 := by
    simpa [prefixWord, tailWord_4189145, baseEnd_4189145] using wordTrace_append hprefix tailTrace_4189145
  have hstable : (prefixWord ++ tailWord_4189145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189145).length < 2 ^ (prefixWord ++ tailWord_4189145).sum := by decide
  have hdescent : baseEnd_4189145 < baseStart_4189145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189159 : List Nat := [1, 1, 5, 2, 2, 1, 3, 3, 1, 2, 2]
def baseStart_4189159 : Nat := 118140960795 + 4189159 * 2 ^ 59
def prefixEnd_4189159 : Nat := 4983230072969 + 3 ^ 40 * 4189159 * 2
def baseEnd_4189159 : Nat := 2151052105108280629846915

theorem tailTrace_4189159 : CollatzResearch.WordTrace tailWord_4189159 prefixEnd_4189159 2151052105108280629846915 := by
  unfold tailWord_4189159
  simp only [CollatzResearch.WordTrace]
  refine ⟨152791181030399869242314531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101860787353599912828209687 152791181030399869242314531)
  ·
    refine ⟨229186771545599803863471797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152791181030399869242314531 229186771545599803863471797)
    ·
      refine ⟨21486259832399981612200481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 229186771545599803863471797 21486259832399981612200481)
      ·
        refine ⟨16114694874299986209150361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21486259832399981612200481 16114694874299986209150361)
        ·
          refine ⟨12086021155724989656862771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16114694874299986209150361 12086021155724989656862771)
          ·
            refine ⟨18129031733587484485294157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12086021155724989656862771 18129031733587484485294157)
            ·
              refine ⟨6798386900095306681985309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18129031733587484485294157 6798386900095306681985309)
              ·
                refine ⟨2549395087535740005744491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6798386900095306681985309 2549395087535740005744491)
                ·
                  refine ⟨3824092631303610008616737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549395087535740005744491 3824092631303610008616737)
                  ·
                    refine ⟨2868069473477707506462553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3824092631303610008616737 2868069473477707506462553)
                    ·
                      refine ⟨2151052105108280629846915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2868069473477707506462553 2151052105108280629846915)
                      ·
                        rfl

theorem cell23_4189159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_4189159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189159 prefixEnd_4189159 := by exact prefixLift 4189159
  have htrace : WordTrace (prefixWord ++ tailWord_4189159) baseStart_4189159 baseEnd_4189159 := by
    simpa [prefixWord, tailWord_4189159, baseEnd_4189159] using wordTrace_append hprefix tailTrace_4189159
  have hstable : (prefixWord ++ tailWord_4189159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189159).length < 2 ^ (prefixWord ++ tailWord_4189159).sum := by decide
  have hdescent : baseEnd_4189159 < baseStart_4189159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189168 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 5, 3, 2]
def baseStart_4189168 : Nat := 118140960795 + 4189168 * 2 ^ 59
def prefixEnd_4189168 : Nat := 4983230072969 + 3 ^ 40 * 4189168 * 2
def baseEnd_4189168 : Nat := 2151056726434171094634373

theorem tailTrace_4189168 : CollatzResearch.WordTrace tailWord_4189168 prefixEnd_4189168 2151056726434171094634373 := by
  unfold tailWord_4189168
  simp only [CollatzResearch.WordTrace]
  refine ⟨76395754643683631889696079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101861006191578175852928105 76395754643683631889696079)
  ·
    refine ⟨114593631965525447834544119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76395754643683631889696079 114593631965525447834544119)
    ·
      refine ⟨171890447948288171751816179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114593631965525447834544119 171890447948288171751816179)
      ·
        refine ⟨257835671922432257627724269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171890447948288171751816179 257835671922432257627724269)
        ·
          refine ⟨96688376970912096610396601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257835671922432257627724269 96688376970912096610396601)
          ·
            refine ⟨72516282728184072457797451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96688376970912096610396601 72516282728184072457797451)
            ·
              refine ⟨108774424092276108686696177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72516282728184072457797451 108774424092276108686696177)
              ·
                refine ⟨81580818069207081515022133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108774424092276108686696177 81580818069207081515022133)
                ·
                  refine ⟨7648201693988163892033325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81580818069207081515022133 7648201693988163892033325)
                  ·
                    refine ⟨2868075635245561459512497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7648201693988163892033325 2868075635245561459512497)
                    ·
                      refine ⟨2151056726434171094634373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2868075635245561459512497 2151056726434171094634373)
                      ·
                        rfl

theorem cell23_4189168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 5, 3, 2].length) (baseStart_4189168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189168 prefixEnd_4189168 := by exact prefixLift 4189168
  have htrace : WordTrace (prefixWord ++ tailWord_4189168) baseStart_4189168 baseEnd_4189168 := by
    simpa [prefixWord, tailWord_4189168, baseEnd_4189168] using wordTrace_append hprefix tailTrace_4189168
  have hstable : (prefixWord ++ tailWord_4189168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189168).length < 2 ^ (prefixWord ++ tailWord_4189168).sum := by decide
  have hdescent : baseEnd_4189168 < baseStart_4189168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189181 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_4189181 : Nat := 118140960795 + 4189181 * 2 ^ 59
def prefixEnd_4189181 : Nat := 4983230072969 + 3 ^ 40 * 4189181 * 2
def baseEnd_4189181 : Nat := 2151063401682679543771813

theorem tailTrace_4189181 : CollatzResearch.WordTrace tailWord_4189181 prefixEnd_4189181 2151063401682679543771813 := by
  unfold tailWord_4189181
  simp only [CollatzResearch.WordTrace]
  refine ⟨152791983436320166999615397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101861322290880111333076931 152791983436320166999615397)
  ·
    refine ⟨28648496894310031312427887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152791983436320166999615397 28648496894310031312427887)
    ·
      refine ⟨42972745341465046968641831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28648496894310031312427887 42972745341465046968641831)
      ·
        refine ⟨64459118012197570452962747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42972745341465046968641831 64459118012197570452962747)
        ·
          refine ⟨96688677018296355679444121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64459118012197570452962747 96688677018296355679444121)
          ·
            refine ⟨72516507763722266759583091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96688677018296355679444121 72516507763722266759583091)
            ·
              refine ⟨108774761645583400139374637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72516507763722266759583091 108774761645583400139374637)
              ·
                refine ⟨40790535617093775052265489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108774761645583400139374637 40790535617093775052265489)
                ·
                  refine ⟨30592901712820331289199117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40790535617093775052265489 30592901712820331289199117)
                  ·
                    refine ⟨11472338142307624233449669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30592901712820331289199117 11472338142307624233449669)
                    ·
                      refine ⟨2151063401682679543771813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11472338142307624233449669 2151063401682679543771813)
                      ·
                        rfl

theorem cell23_4189181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_4189181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189181 prefixEnd_4189181 := by exact prefixLift 4189181
  have htrace : WordTrace (prefixWord ++ tailWord_4189181) baseStart_4189181 baseEnd_4189181 := by
    simpa [prefixWord, tailWord_4189181, baseEnd_4189181] using wordTrace_append hprefix tailTrace_4189181
  have hstable : (prefixWord ++ tailWord_4189181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189181).length < 2 ^ (prefixWord ++ tailWord_4189181).sum := by decide
  have hdescent : baseEnd_4189181 < baseStart_4189181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189186 : List Nat := [3, 4, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_4189186 : Nat := 118140960795 + 4189186 * 2 ^ 59
def prefixEnd_4189186 : Nat := 4983230072969 + 3 ^ 40 * 4189186 * 2
def baseEnd_4189186 : Nat := 717021989695317341403097

theorem tailTrace_4189186 : CollatzResearch.WordTrace tailWord_4189186 prefixEnd_4189186 717021989695317341403097 := by
  unfold tailWord_4189186
  simp only [CollatzResearch.WordTrace]
  refine ⟨38198041450325513213386853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101861443867534701902364941 38198041450325513213386853)
  ·
    refine ⟨7162132771936033727510035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38198041450325513213386853 7162132771936033727510035)
    ·
      refine ⟨10743199157904050591265053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7162132771936033727510035 10743199157904050591265053)
      ·
        refine ⟨4028699684214018971724395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10743199157904050591265053 4028699684214018971724395)
        ·
          refine ⟨6043049526321028457586593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4028699684214018971724395 6043049526321028457586593)
          ·
            refine ⟨4532287144740771343189945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6043049526321028457586593 4532287144740771343189945)
            ·
              refine ⟨3399215358555578507392459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4532287144740771343189945 3399215358555578507392459)
              ·
                refine ⟨5098823037833367761088689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3399215358555578507392459 5098823037833367761088689)
                ·
                  refine ⟨3824117278375025820816517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5098823037833367761088689 3824117278375025820816517)
                  ·
                    refine ⟨717021989695317341403097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3824117278375025820816517 717021989695317341403097)
                    ·
                      rfl

theorem cell23_4189186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_4189186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189186 prefixEnd_4189186 := by exact prefixLift 4189186
  have htrace : WordTrace (prefixWord ++ tailWord_4189186) baseStart_4189186 baseEnd_4189186 := by
    simpa [prefixWord, tailWord_4189186, baseEnd_4189186] using wordTrace_append hprefix tailTrace_4189186
  have hstable : (prefixWord ++ tailWord_4189186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189186).length < 2 ^ (prefixWord ++ tailWord_4189186).sum := by decide
  have hdescent : baseEnd_4189186 < baseStart_4189186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189191 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 1, 8]
def baseStart_4189191 : Nat := 118140960795 + 4189191 * 2 ^ 59
def prefixEnd_4189191 : Nat := 4983230072969 + 3 ^ 40 * 4189191 * 2
def baseEnd_4189191 : Nat := 717022845496408168215589

theorem tailTrace_4189191 : CollatzResearch.WordTrace tailWord_4189191 prefixEnd_4189191 717022845496408168215589 := by
  unfold tailWord_4189191
  simp only [CollatzResearch.WordTrace]
  refine ⟨152792348166283938707479427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101861565444189292471652951 152792348166283938707479427)
  ·
    refine ⟨229188522249425908061219141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152792348166283938707479427 229188522249425908061219141)
    ·
      refine ⟨42972847921767357761478589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229188522249425908061219141 42972847921767357761478589)
      ·
        refine ⟨16114817970662759160554471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42972847921767357761478589 16114817970662759160554471)
        ·
          refine ⟨24172226955994138740831707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16114817970662759160554471 24172226955994138740831707)
          ·
            refine ⟨36258340433991208111247561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24172226955994138740831707 36258340433991208111247561)
            ·
              refine ⟨27193755325493406083435671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36258340433991208111247561 27193755325493406083435671)
              ·
                refine ⟨40790632988240109125153507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27193755325493406083435671 40790632988240109125153507)
                ·
                  refine ⟨61185949482360163687730261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40790632988240109125153507 61185949482360163687730261)
                  ·
                    refine ⟨717022845496408168215589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61185949482360163687730261 717022845496408168215589)
                    ·
                      rfl

theorem cell23_4189191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_4189191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189191 prefixEnd_4189191 := by exact prefixLift 4189191
  have htrace : WordTrace (prefixWord ++ tailWord_4189191) baseStart_4189191 baseEnd_4189191 := by
    simpa [prefixWord, tailWord_4189191, baseEnd_4189191] using wordTrace_append hprefix tailTrace_4189191
  have hstable : (prefixWord ++ tailWord_4189191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189191).length < 2 ^ (prefixWord ++ tailWord_4189191).sum := by decide
  have hdescent : baseEnd_4189191 < baseStart_4189191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189192 : List Nat := [2, 1, 3, 2, 1, 3, 4, 1, 2, 1, 3]
def baseStart_4189192 : Nat := 118140960795 + 4189192 * 2 ^ 59
def prefixEnd_4189192 : Nat := 4983230072969 + 3 ^ 40 * 4189192 * 2
def baseEnd_4189192 : Nat := 2151069049969879000734263

theorem tailTrace_4189192 : CollatzResearch.WordTrace tailWord_4189192 prefixEnd_4189192 2151069049969879000734263 := by
  unfold tailWord_4189192
  simp only [CollatzResearch.WordTrace]
  refine ⟨76396192319640157939132915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101861589759520210585510553 76396192319640157939132915)
  ·
    refine ⟨114594288479460236908699373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76396192319640157939132915 114594288479460236908699373)
    ·
      refine ⟨42972858179797588840762265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114594288479460236908699373 42972858179797588840762265)
      ·
        refine ⟨32229643634848191630571699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42972858179797588840762265 32229643634848191630571699)
        ·
          refine ⟨48344465452272287445857549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32229643634848191630571699 48344465452272287445857549)
          ·
            refine ⟨18129174544602107792196581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48344465452272287445857549 18129174544602107792196581)
            ·
              refine ⟨3399220227112895211036859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18129174544602107792196581 3399220227112895211036859)
              ·
                refine ⟨5098830340669342816555289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3399220227112895211036859 5098830340669342816555289)
                ·
                  refine ⟨3824122755502007112416467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5098830340669342816555289 3824122755502007112416467)
                  ·
                    refine ⟨5736184133253010668624701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3824122755502007112416467 5736184133253010668624701)
                    ·
                      refine ⟨2151069049969879000734263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5736184133253010668624701 2151069049969879000734263)
                      ·
                        rfl

theorem cell23_4189192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_4189192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189192 prefixEnd_4189192 := by exact prefixLift 4189192
  have htrace : WordTrace (prefixWord ++ tailWord_4189192) baseStart_4189192 baseEnd_4189192 := by
    simpa [prefixWord, tailWord_4189192, baseEnd_4189192] using wordTrace_append hprefix tailTrace_4189192
  have hstable : (prefixWord ++ tailWord_4189192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189192).length < 2 ^ (prefixWord ++ tailWord_4189192).sum := by decide
  have hdescent : baseEnd_4189192 < baseStart_4189192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189215 : List Nat := [1, 1, 2, 4, 1, 4, 1, 2, 1, 4, 2]
def baseStart_4189215 : Nat := 118140960795 + 4189215 * 2 ^ 59
def prefixEnd_4189215 : Nat := 4983230072969 + 3 ^ 40 * 4189215 * 2
def baseEnd_4189215 : Nat := 2151080860024932410746657

theorem tailTrace_4189215 : CollatzResearch.WordTrace tailWord_4189215 prefixEnd_4189215 2151080860024932410746657 := by
  unfold tailWord_4189215
  simp only [CollatzResearch.WordTrace]
  refine ⟨152793223518196990806353099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101862149012131327204235399 152793223518196990806353099)
  ·
    refine ⟨229189835277295486209529649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152793223518196990806353099 229189835277295486209529649)
    ·
      refine ⟨171892376457971614657147237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229189835277295486209529649 171892376457971614657147237)
      ·
        refine ⟨32229820585869677748215107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171892376457971614657147237 32229820585869677748215107)
        ·
          refine ⟨48344730878804516622322661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32229820585869677748215107 48344730878804516622322661)
          ·
            refine ⟨9064637039775846866685499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48344730878804516622322661 9064637039775846866685499)
            ·
              refine ⟨13596955559663770300028249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9064637039775846866685499 13596955559663770300028249)
              ·
                refine ⟨10197716669747827725021187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13596955559663770300028249 10197716669747827725021187)
                ·
                  refine ⟨15296575004621741587531781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10197716669747827725021187 15296575004621741587531781)
                  ·
                    refine ⟨2868107813366576547662209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15296575004621741587531781 2868107813366576547662209)
                    ·
                      refine ⟨2151080860024932410746657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2868107813366576547662209 2151080860024932410746657)
                      ·
                        rfl

theorem cell23_4189215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_4189215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189215 prefixEnd_4189215 := by exact prefixLift 4189215
  have htrace : WordTrace (prefixWord ++ tailWord_4189215) baseStart_4189215 baseEnd_4189215 := by
    simpa [prefixWord, tailWord_4189215, baseEnd_4189215] using wordTrace_append hprefix tailTrace_4189215
  have hstable : (prefixWord ++ tailWord_4189215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189215).length < 2 ^ (prefixWord ++ tailWord_4189215).sum := by decide
  have hdescent : baseEnd_4189215 < baseStart_4189215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189218 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_4189218 : Nat := 118140960795 + 4189218 * 2 ^ 59
def prefixEnd_4189218 : Nat := 4983230072969 + 3 ^ 40 * 4189218 * 2
def baseEnd_4189218 : Nat := 2151082400466895899009143

theorem tailTrace_4189218 : CollatzResearch.WordTrace tailWord_4189218 prefixEnd_4189218 2151082400466895899009143 := by
  unfold tailWord_4189218
  simp only [CollatzResearch.WordTrace]
  refine ⟨38198333234296530579678077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101862221958124081545808205 38198333234296530579678077)
  ·
    refine ⟨14324374962861198967379279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38198333234296530579678077 14324374962861198967379279)
    ·
      refine ⟨21486562444291798451068919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14324374962861198967379279 21486562444291798451068919)
      ·
        refine ⟨32229843666437697676603379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21486562444291798451068919 32229843666437697676603379)
        ·
          refine ⟨48344765499656546514905069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32229843666437697676603379 48344765499656546514905069)
          ·
            refine ⟨18129287062371204943089401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48344765499656546514905069 18129287062371204943089401)
            ·
              refine ⟨13596965296778403707317051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18129287062371204943089401 13596965296778403707317051)
              ·
                refine ⟨20395447945167605560975577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13596965296778403707317051 20395447945167605560975577)
                ·
                  refine ⟨15296585958875704170731683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20395447945167605560975577 15296585958875704170731683)
                  ·
                    refine ⟨22944878938313556256097525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15296585958875704170731683 22944878938313556256097525)
                    ·
                      refine ⟨2151082400466895899009143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22944878938313556256097525 2151082400466895899009143)
                      ·
                        rfl

theorem cell23_4189218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_4189218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189218 prefixEnd_4189218 := by exact prefixLift 4189218
  have htrace : WordTrace (prefixWord ++ tailWord_4189218) baseStart_4189218 baseEnd_4189218 := by
    simpa [prefixWord, tailWord_4189218, baseEnd_4189218] using wordTrace_append hprefix tailTrace_4189218
  have hstable : (prefixWord ++ tailWord_4189218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189218).length < 2 ^ (prefixWord ++ tailWord_4189218).sum := by decide
  have hdescent : baseEnd_4189218 < baseStart_4189218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189232 : List Nat := [2, 1, 1, 1, 2, 4, 4, 2, 2, 2, 2]
def baseStart_4189232 : Nat := 118140960795 + 4189232 * 2 ^ 59
def prefixEnd_4189232 : Nat := 4983230072969 + 3 ^ 40 * 4189232 * 2
def baseEnd_4189232 : Nat := 2151089589196058844234079

theorem tailTrace_4189232 : CollatzResearch.WordTrace tailWord_4189232 prefixEnd_4189232 2151089589196058844234079 := by
  unfold tailWord_4189232
  simp only [CollatzResearch.WordTrace]
  refine ⟨76396921779567701354860975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101862562372756935139814633 76396921779567701354860975)
  ·
    refine ⟨114595382669351552032291463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76396921779567701354860975 114595382669351552032291463)
    ·
      refine ⟨171893074004027328048437195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114595382669351552032291463 171893074004027328048437195)
      ·
        refine ⟨257839611006040992072655793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171893074004027328048437195 257839611006040992072655793)
        ·
          refine ⟨193379708254530744054491845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257839611006040992072655793 193379708254530744054491845)
          ·
            refine ⟨36258695297724514510217221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193379708254530744054491845 36258695297724514510217221)
            ·
              refine ⟨6798505368323346470665729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36258695297724514510217221 6798505368323346470665729)
              ·
                refine ⟨5098879026242509852999297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6798505368323346470665729 5098879026242509852999297)
                ·
                  refine ⟨3824159269681882389749473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5098879026242509852999297 3824159269681882389749473)
                  ·
                    refine ⟨2868119452261411792312105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3824159269681882389749473 2868119452261411792312105)
                    ·
                      refine ⟨2151089589196058844234079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2868119452261411792312105 2151089589196058844234079)
                      ·
                        rfl

theorem cell23_4189232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 2, 2, 2].length) (baseStart_4189232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189232 prefixEnd_4189232 := by exact prefixLift 4189232
  have htrace : WordTrace (prefixWord ++ tailWord_4189232) baseStart_4189232 baseEnd_4189232 := by
    simpa [prefixWord, tailWord_4189232, baseEnd_4189232] using wordTrace_append hprefix tailTrace_4189232
  have hstable : (prefixWord ++ tailWord_4189232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189232).length < 2 ^ (prefixWord ++ tailWord_4189232).sum := by decide
  have hdescent : baseEnd_4189232 < baseStart_4189232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189248 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 3]
def baseStart_4189248 : Nat := 118140960795 + 4189248 * 2 ^ 59
def prefixEnd_4189248 : Nat := 4983230072969 + 3 ^ 40 * 4189248 * 2
def baseEnd_4189248 : Nat := 2151097804886530781634005

theorem tailTrace_4189248 : CollatzResearch.WordTrace tailWord_4189248 prefixEnd_4189248 2151097804886530781634005 := by
  unfold tailWord_4189248
  simp only [CollatzResearch.WordTrace]
  refine ⟨76397213563538718721152199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101862951418051624961536265 76397213563538718721152199)
  ·
    refine ⟨114595820345308078081728299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76397213563538718721152199 114595820345308078081728299)
    ·
      refine ⟨171893730517962117122592449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114595820345308078081728299 171893730517962117122592449)
      ·
        refine ⟨128920297888471587841944337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171893730517962117122592449 128920297888471587841944337)
        ·
          refine ⟨96690223416353690881458253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128920297888471587841944337 96690223416353690881458253)
          ·
            refine ⟨36258833781132634080546845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96690223416353690881458253 36258833781132634080546845)
            ·
              refine ⟨13597062667924737780205067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36258833781132634080546845 13597062667924737780205067)
              ·
                refine ⟨20395594001887106670307601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13597062667924737780205067 20395594001887106670307601)
                ·
                  refine ⟨15296695501415330002730701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20395594001887106670307601 15296695501415330002730701)
                  ·
                    refine ⟨5736260813030748751024013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15296695501415330002730701 5736260813030748751024013)
                    ·
                      refine ⟨2151097804886530781634005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5736260813030748751024013 2151097804886530781634005)
                      ·
                        rfl

theorem cell23_4189248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_4189248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189248 prefixEnd_4189248 := by exact prefixLift 4189248
  have htrace : WordTrace (prefixWord ++ tailWord_4189248) baseStart_4189248 baseEnd_4189248 := by
    simpa [prefixWord, tailWord_4189248, baseEnd_4189248] using wordTrace_append hprefix tailTrace_4189248
  have hstable : (prefixWord ++ tailWord_4189248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189248).length < 2 ^ (prefixWord ++ tailWord_4189248).sum := by decide
  have hdescent : baseEnd_4189248 < baseStart_4189248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189251 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 1, 7]
def baseStart_4189251 : Nat := 118140960795 + 4189251 * 2 ^ 59
def prefixEnd_4189251 : Nat := 4983230072969 + 3 ^ 40 * 4189251 * 2
def baseEnd_4189251 : Nat := 717033115109498089965497

theorem tailTrace_4189251 : CollatzResearch.WordTrace tailWord_4189251 prefixEnd_4189251 717033115109498089965497 := by
  unfold tailWord_4189251
  simp only [CollatzResearch.WordTrace]
  refine ⟨152794536546066568954663607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101863024364044379303109071 152794536546066568954663607)
  ·
    refine ⟨229191804819099853431995411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152794536546066568954663607 229191804819099853431995411)
    ·
      refine ⟨343787707228649780147993117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229191804819099853431995411 343787707228649780147993117)
      ·
        refine ⟨128920390210743667555497419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343787707228649780147993117 128920390210743667555497419)
        ·
          refine ⟨193380585316115501333246129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128920390210743667555497419 193380585316115501333246129)
          ·
            refine ⟨145035438987086625999934597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193380585316115501333246129 145035438987086625999934597)
            ·
              refine ⟨27194144810078742374987737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145035438987086625999934597 27194144810078742374987737)
              ·
                refine ⟨20395608607559056781240803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27194144810078742374987737 20395608607559056781240803)
                ·
                  refine ⟨30593412911338585171861205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20395608607559056781240803 30593412911338585171861205)
                  ·
                    refine ⟨717033115109498089965497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30593412911338585171861205 717033115109498089965497)
                    ·
                      rfl

theorem cell23_4189251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 7].length) (baseStart_4189251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189251 prefixEnd_4189251 := by exact prefixLift 4189251
  have htrace : WordTrace (prefixWord ++ tailWord_4189251) baseStart_4189251 baseEnd_4189251 := by
    simpa [prefixWord, tailWord_4189251, baseEnd_4189251] using wordTrace_append hprefix tailTrace_4189251
  have hstable : (prefixWord ++ tailWord_4189251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189251).length < 2 ^ (prefixWord ++ tailWord_4189251).sum := by decide
  have hdescent : baseEnd_4189251 < baseStart_4189251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189270 : List Nat := [5, 2, 2, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_4189270 : Nat := 118140960795 + 4189270 * 2 ^ 59
def prefixEnd_4189270 : Nat := 4983230072969 + 3 ^ 40 * 4189270 * 2
def baseEnd_4189270 : Nat := 2151109101460929695558905

theorem tailTrace_4189270 : CollatzResearch.WordTrace tailWord_4189270 prefixEnd_4189270 2151109101460929695558905 := by
  unfold tailWord_4189270
  simp only [CollatzResearch.WordTrace]
  refine ⟨9549701845812358449975329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101863486355331823466403509 9549701845812358449975329)
  ·
    refine ⟨7162276384359268837481497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9549701845812358449975329 7162276384359268837481497)
    ·
      refine ⟨5371707288269451628111123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7162276384359268837481497 5371707288269451628111123)
      ·
        refine ⟨8057560932404177442166685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5371707288269451628111123 8057560932404177442166685)
        ·
          refine ⟨3021585349651566540812507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8057560932404177442166685 3021585349651566540812507)
          ·
            refine ⟨4532378024477349811218761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3021585349651566540812507 4532378024477349811218761)
            ·
              refine ⟨3399283518358012358414071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4532378024477349811218761 3399283518358012358414071)
              ·
                refine ⟨5098925277537018537621107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3399283518358012358414071 5098925277537018537621107)
                ·
                  refine ⟨7648387916305527806431661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098925277537018537621107 7648387916305527806431661)
                  ·
                    refine ⟨2868145468614572927411873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7648387916305527806431661 2868145468614572927411873)
                    ·
                      refine ⟨2151109101460929695558905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2868145468614572927411873 2151109101460929695558905)
                      ·
                        rfl

theorem cell23_4189270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_4189270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189270 prefixEnd_4189270 := by exact prefixLift 4189270
  have htrace : WordTrace (prefixWord ++ tailWord_4189270) baseStart_4189270 baseEnd_4189270 := by
    simpa [prefixWord, tailWord_4189270, baseEnd_4189270] using wordTrace_append hprefix tailTrace_4189270
  have hstable : (prefixWord ++ tailWord_4189270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189270).length < 2 ^ (prefixWord ++ tailWord_4189270).sum := by decide
  have hdescent : baseEnd_4189270 < baseStart_4189270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189308 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 3, 4, 3]
def baseStart_4189308 : Nat := 118140960795 + 4189308 * 2 ^ 59
def prefixEnd_4189308 : Nat := 4983230072969 + 3 ^ 40 * 4189308 * 2
def baseEnd_4189308 : Nat := 2151128613725800546883729

theorem tailTrace_4189308 : CollatzResearch.WordTrace tailWord_4189308 prefixEnd_4189308 2151128613725800546883729 := by
  unfold tailWord_4189308
  simp only [CollatzResearch.WordTrace]
  refine ⟨76398307753430033844744289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101864410337906711792992385 76398307753430033844744289)
  ·
    refine ⟨57298730815072525383558217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76398307753430033844744289 57298730815072525383558217)
    ·
      refine ⟨42974048111304394037668663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57298730815072525383558217 42974048111304394037668663)
      ·
        refine ⟨64461072166956591056502995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42974048111304394037668663 64461072166956591056502995)
        ·
          refine ⟨96691608250434886584754493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64461072166956591056502995 96691608250434886584754493)
          ·
            refine ⟨36259353093913082469282935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96691608250434886584754493 36259353093913082469282935)
            ·
              refine ⟨54389029640869623703924403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36259353093913082469282935 54389029640869623703924403)
              ·
                refine ⟨81583544461304435555886605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54389029640869623703924403 81583544461304435555886605)
                ·
                  refine ⟨30593829172989163333457477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81583544461304435555886605 30593829172989163333457477)
                  ·
                    refine ⟨5736342969935468125023277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30593829172989163333457477 5736342969935468125023277)
                    ·
                      refine ⟨2151128613725800546883729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5736342969935468125023277 2151128613725800546883729)
                      ·
                        rfl

theorem cell23_4189308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_4189308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189308 prefixEnd_4189308 := by exact prefixLift 4189308
  have htrace : WordTrace (prefixWord ++ tailWord_4189308) baseStart_4189308 baseEnd_4189308 := by
    simpa [prefixWord, tailWord_4189308, baseEnd_4189308] using wordTrace_append hprefix tailTrace_4189308
  have hstable : (prefixWord ++ tailWord_4189308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189308).length < 2 ^ (prefixWord ++ tailWord_4189308).sum := by decide
  have hdescent : baseEnd_4189308 < baseStart_4189308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189342 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_4189342 : Nat := 118140960795 + 4189342 * 2 ^ 59
def prefixEnd_4189342 : Nat := 4983230072969 + 3 ^ 40 * 4189342 * 2
def baseEnd_4189342 : Nat := 2151146072068053413858573

theorem tailTrace_4189342 : CollatzResearch.WordTrace tailWord_4189342 prefixEnd_4189342 2151146072068053413858573 := by
  unfold tailWord_4189342
  simp only [CollatzResearch.WordTrace]
  refine ⟨19099731948592111437028285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101865237059157927664150853 19099731948592111437028285)
  ·
    refine ⟨7162399480722041788885607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19099731948592111437028285 7162399480722041788885607)
    ·
      refine ⟨10743599221083062683328411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7162399480722041788885607 10743599221083062683328411)
      ·
        refine ⟨16115398831624594024992617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10743599221083062683328411 16115398831624594024992617)
        ·
          refine ⟨12086549123718445518744463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16115398831624594024992617 12086549123718445518744463)
          ·
            refine ⟨18129823685577668278116695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12086549123718445518744463 18129823685577668278116695)
            ·
              refine ⟨27194735528366502417175043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18129823685577668278116695 27194735528366502417175043)
              ·
                refine ⟨40792103292549753625762565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27194735528366502417175043 40792103292549753625762565)
                ·
                  refine ⟨7648519367353078804830481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40792103292549753625762565 7648519367353078804830481)
                  ·
                    refine ⟨5736389525514809103622861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7648519367353078804830481 5736389525514809103622861)
                    ·
                      refine ⟨2151146072068053413858573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5736389525514809103622861 2151146072068053413858573)
                      ·
                        rfl

theorem cell23_4189342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_4189342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189342 prefixEnd_4189342 := by exact prefixLift 4189342
  have htrace : WordTrace (prefixWord ++ tailWord_4189342) baseStart_4189342 baseEnd_4189342 := by
    simpa [prefixWord, tailWord_4189342, baseEnd_4189342] using wordTrace_append hprefix tailTrace_4189342
  have hstable : (prefixWord ++ tailWord_4189342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189342).length < 2 ^ (prefixWord ++ tailWord_4189342).sum := by decide
  have hdescent : baseEnd_4189342 < baseStart_4189342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189349 : List Nat := [1, 3, 1, 2, 1, 5, 3, 2, 1, 4]
def baseStart_4189349 : Nat := 118140960795 + 4189349 * 2 ^ 59
def prefixEnd_4189349 : Nat := 4983230072969 + 3 ^ 40 * 4189349 * 2
def baseEnd_4189349 : Nat := 717049888810878295490347

theorem tailTrace_4189349 : CollatzResearch.WordTrace tailWord_4189349 prefixEnd_4189349 717049888810878295490347 := by
  unfold tailWord_4189349
  simp only [CollatzResearch.WordTrace]
  refine ⟨152798110899711531691731101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101865407266474354461154067 152798110899711531691731101)
  ·
    refine ⟨57299291587391824384399163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152798110899711531691731101 57299291587391824384399163)
    ·
      refine ⟨85948937381087736576598745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57299291587391824384399163 85948937381087736576598745)
      ·
        refine ⟨64461703035815802432449059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85948937381087736576598745 64461703035815802432449059)
        ·
          refine ⟨96692554553723703648673589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64461703035815802432449059 96692554553723703648673589)
          ·
            refine ⟨9064926989411597217063149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96692554553723703648673589 9064926989411597217063149)
            ·
              refine ⟨3399347621029348956398681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9064926989411597217063149 3399347621029348956398681)
              ·
                refine ⟨2549510715772011717299011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3399347621029348956398681 2549510715772011717299011)
                ·
                  refine ⟨3824266073658017575948517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549510715772011717299011 3824266073658017575948517)
                  ·
                    refine ⟨717049888810878295490347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3824266073658017575948517 717049888810878295490347)
                    ·
                      rfl

theorem cell23_4189349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 1, 4].length) (baseStart_4189349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189349 prefixEnd_4189349 := by exact prefixLift 4189349
  have htrace : WordTrace (prefixWord ++ tailWord_4189349) baseStart_4189349 baseEnd_4189349 := by
    simpa [prefixWord, tailWord_4189349, baseEnd_4189349] using wordTrace_append hprefix tailTrace_4189349
  have hstable : (prefixWord ++ tailWord_4189349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189349).length < 2 ^ (prefixWord ++ tailWord_4189349).sum := by decide
  have hdescent : baseEnd_4189349 < baseStart_4189349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189362 : List Nat := [3, 2, 1, 1, 1, 6, 2, 1, 6]
def baseStart_4189362 : Nat := 118140960795 + 4189362 * 2 ^ 59
def prefixEnd_4189362 : Nat := 4983230072969 + 3 ^ 40 * 4189362 * 2
def baseEnd_4189362 : Nat := 239017371297904815067609

theorem tailTrace_4189362 : CollatzResearch.WordTrace tailWord_4189362 prefixEnd_4189362 239017371297904815067609 := by
  unfold tailWord_4189362
  simp only [CollatzResearch.WordTrace]
  refine ⟨38199646262166108727988585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101865723365776289941302893 38199646262166108727988585)
  ·
    refine ⟨28649734696624581545991439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38199646262166108727988585 28649734696624581545991439)
    ·
      refine ⟨42974602044936872318987159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28649734696624581545991439 42974602044936872318987159)
      ·
        refine ⟨64461903067405308478480739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42974602044936872318987159 64461903067405308478480739)
        ·
          refine ⟨96692854601107962717721109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64461903067405308478480739 96692854601107962717721109)
          ·
            refine ⟨4532477559426935752393177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96692854601107962717721109 4532477559426935752393177)
            ·
              refine ⟨3399358169570201814294883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4532477559426935752393177 3399358169570201814294883)
              ·
                refine ⟨5099037254355302721442325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3399358169570201814294883 5099037254355302721442325)
                ·
                  refine ⟨239017371297904815067609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5099037254355302721442325 239017371297904815067609)
                  ·
                    rfl

theorem cell23_4189362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_4189362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189362 prefixEnd_4189362 := by exact prefixLift 4189362
  have htrace : WordTrace (prefixWord ++ tailWord_4189362) baseStart_4189362 baseEnd_4189362 := by
    simpa [prefixWord, tailWord_4189362, baseEnd_4189362] using wordTrace_append hprefix tailTrace_4189362
  have hstable : (prefixWord ++ tailWord_4189362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189362).length < 2 ^ (prefixWord ++ tailWord_4189362).sum := by decide
  have hdescent : baseEnd_4189362 < baseStart_4189362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189375 : List Nat := [1, 1, 2, 2, 2, 2, 5, 2, 1, 5]
def baseStart_4189375 : Nat := 118140960795 + 4189375 * 2 ^ 59
def prefixEnd_4189375 : Nat := 4983230072969 + 3 ^ 40 * 4189375 * 2
def baseEnd_4189375 : Nat := 717054338976550594915307

theorem tailTrace_4189375 : CollatzResearch.WordTrace tailWord_4189375 prefixEnd_4189375 717054338976550594915307 := by
  unfold tailWord_4189375
  simp only [CollatzResearch.WordTrace]
  refine ⟨152799059197617338132177579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101866039465078225421451719 152799059197617338132177579)
  ·
    refine ⟨229198588796426007198266369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152799059197617338132177579 229198588796426007198266369)
    ·
      refine ⟨171898941597319505398699777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229198588796426007198266369 171898941597319505398699777)
      ·
        refine ⟨128924206197989629049024833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171898941597319505398699777 128924206197989629049024833)
        ·
          refine ⟨96693154648492221786768625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128924206197989629049024833 96693154648492221786768625)
          ·
            refine ⟨72519865986369166340076469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96693154648492221786768625 72519865986369166340076469)
            ·
              refine ⟨6798737436222109344382169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72519865986369166340076469 6798737436222109344382169)
              ·
                refine ⟨5099053077166582008286627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6798737436222109344382169 5099053077166582008286627)
                ·
                  refine ⟨7648579615749873012429941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5099053077166582008286627 7648579615749873012429941)
                  ·
                    refine ⟨717054338976550594915307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7648579615749873012429941 717054338976550594915307)
                    ·
                      rfl

theorem cell23_4189375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 5].length) (baseStart_4189375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189375 prefixEnd_4189375 := by exact prefixLift 4189375
  have htrace : WordTrace (prefixWord ++ tailWord_4189375) baseStart_4189375 baseEnd_4189375 := by
    simpa [prefixWord, tailWord_4189375, baseEnd_4189375] using wordTrace_append hprefix tailTrace_4189375
  have hstable : (prefixWord ++ tailWord_4189375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189375).length < 2 ^ (prefixWord ++ tailWord_4189375).sum := by decide
  have hdescent : baseEnd_4189375 < baseStart_4189375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189422 : List Nat := [4, 1, 2, 1, 1, 1, 4, 3, 2, 4]
def baseStart_4189422 : Nat := 118140960795 + 4189422 * 2 ^ 59
def prefixEnd_4189422 : Nat := 4983230072969 + 3 ^ 40 * 4189422 * 2
def baseEnd_4189422 : Nat := 717062383506804366952735

theorem tailTrace_4189422 : CollatzResearch.WordTrace tailWord_4189422 prefixEnd_4189422 717062383506804366952735 := by
  unfold tailWord_4189422
  simp only [CollatzResearch.WordTrace]
  refine ⟨19100096678555883144892315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101867182285631376772759013 19100096678555883144892315)
  ·
    refine ⟨28650145017833824717338473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19100096678555883144892315 28650145017833824717338473)
    ·
      refine ⟨21487608763375368538003855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28650145017833824717338473 21487608763375368538003855)
      ·
        refine ⟨32231413145063052807005783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21487608763375368538003855 32231413145063052807005783)
        ·
          refine ⟨48347119717594579210508675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32231413145063052807005783 48347119717594579210508675)
          ·
            refine ⟨72520679576391868815763013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48347119717594579210508675 72520679576391868815763013)
            ·
              refine ⟨13597627420573475402955565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72520679576391868815763013 13597627420573475402955565)
              ·
                refine ⟨5099110282715053276108337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13597627420573475402955565 5099110282715053276108337)
                ·
                  refine ⟨3824332712036289957081253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5099110282715053276108337 3824332712036289957081253)
                  ·
                    refine ⟨717062383506804366952735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3824332712036289957081253 717062383506804366952735)
                    ·
                      rfl

theorem cell23_4189422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_4189422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189422 prefixEnd_4189422 := by exact prefixLift 4189422
  have htrace : WordTrace (prefixWord ++ tailWord_4189422) baseStart_4189422 baseEnd_4189422 := by
    simpa [prefixWord, tailWord_4189422, baseEnd_4189422] using wordTrace_append hprefix tailTrace_4189422
  have hstable : (prefixWord ++ tailWord_4189422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189422).length < 2 ^ (prefixWord ++ tailWord_4189422).sum := by decide
  have hdescent : baseEnd_4189422 < baseStart_4189422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189445 : List Nat := [1, 3, 1, 1, 2, 1, 3, 4, 1, 3, 3]
def baseStart_4189445 : Nat := 118140960795 + 4189445 * 2 ^ 59
def prefixEnd_4189445 : Nat := 4983230072969 + 3 ^ 40 * 4189445 * 2
def baseEnd_4189445 : Nat := 2151198960575466510870599

theorem tailTrace_4189445 : CollatzResearch.WordTrace tailWord_4189445 prefixEnd_4189445 2151198960575466510870599 := by
  unfold tailWord_4189445
  simp only [CollatzResearch.WordTrace]
  refine ⟨152801612307363740087225789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101867741538242493391483859 152801612307363740087225789)
  ·
    refine ⟨57300604615261402532709671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152801612307363740087225789 57300604615261402532709671)
    ·
      refine ⟨85950906922892103799064507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57300604615261402532709671 85950906922892103799064507)
      ·
        refine ⟨128926360384338155698596761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85950906922892103799064507 128926360384338155698596761)
        ·
          refine ⟨96694770288253616773947571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128926360384338155698596761 96694770288253616773947571)
          ·
            refine ⟨145042155432380425160921357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96694770288253616773947571 145042155432380425160921357)
            ·
              refine ⟨54390808287142659435345509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145042155432380425160921357 54390808287142659435345509)
              ·
                refine ⟨10198276553839248644127283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54390808287142659435345509 10198276553839248644127283)
                ·
                  refine ⟨15297414830758872966190925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10198276553839248644127283 15297414830758872966190925)
                  ·
                    refine ⟨5736530561534577362321597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15297414830758872966190925 5736530561534577362321597)
                    ·
                      refine ⟨2151198960575466510870599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5736530561534577362321597 2151198960575466510870599)
                      ·
                        rfl

theorem cell23_4189445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_4189445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189445 prefixEnd_4189445 := by exact prefixLift 4189445
  have htrace : WordTrace (prefixWord ++ tailWord_4189445) baseStart_4189445 baseEnd_4189445 := by
    simpa [prefixWord, tailWord_4189445, baseEnd_4189445] using wordTrace_append hprefix tailTrace_4189445
  have hstable : (prefixWord ++ tailWord_4189445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189445).length < 2 ^ (prefixWord ++ tailWord_4189445).sum := by decide
  have hdescent : baseEnd_4189445 < baseStart_4189445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189489 : List Nat := [1, 2, 2, 3, 3, 1, 1, 4, 1, 3, 2]
def baseStart_4189489 : Nat := 118140960795 + 4189489 * 2 ^ 59
def prefixEnd_4189489 : Nat := 4983230072969 + 3 ^ 40 * 4189489 * 2
def baseEnd_4189489 : Nat := 2151221553724264338720397

theorem tailTrace_4189489 : CollatzResearch.WordTrace tailWord_4189489 prefixEnd_4189489 2151221553724264338720397 := by
  unfold tailWord_4189489
  simp only [CollatzResearch.WordTrace]
  refine ⟨152803217119204335601827521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101868811412802890401218347 152803217119204335601827521)
  ·
    refine ⟨114602412839403251701370641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152803217119204335601827521 114602412839403251701370641)
    ·
      refine ⟨85951809629552438776027981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114602412839403251701370641 85951809629552438776027981)
      ·
        refine ⟨32231928611082164541010493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85951809629552438776027981 32231928611082164541010493)
        ·
          refine ⟨12086973229155811702878935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32231928611082164541010493 12086973229155811702878935)
          ·
            refine ⟨18130459843733717554318403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12086973229155811702878935 18130459843733717554318403)
            ·
              refine ⟨27195689765600576331477605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18130459843733717554318403 27195689765600576331477605)
              ·
                refine ⟨5099191831050108062152051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27195689765600576331477605 5099191831050108062152051)
                ·
                  refine ⟨7648787746575162093228077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5099191831050108062152051 7648787746575162093228077)
                  ·
                    refine ⟨2868295404965685784960529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7648787746575162093228077 2868295404965685784960529)
                    ·
                      refine ⟨2151221553724264338720397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2868295404965685784960529 2151221553724264338720397)
                      ·
                        rfl

theorem cell23_4189489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_4189489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189489 prefixEnd_4189489 := by exact prefixLift 4189489
  have htrace : WordTrace (prefixWord ++ tailWord_4189489) baseStart_4189489 baseEnd_4189489 := by
    simpa [prefixWord, tailWord_4189489, baseEnd_4189489] using wordTrace_append hprefix tailTrace_4189489
  have hstable : (prefixWord ++ tailWord_4189489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189489).length < 2 ^ (prefixWord ++ tailWord_4189489).sum := by decide
  have hdescent : baseEnd_4189489 < baseStart_4189489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189535 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 3]
def baseStart_4189535 : Nat := 118140960795 + 4189535 * 2 ^ 59
def prefixEnd_4189535 : Nat := 4983230072969 + 3 ^ 40 * 4189535 * 2
def baseEnd_4189535 : Nat := 2151245173834371158745185

theorem tailTrace_4189535 : CollatzResearch.WordTrace tailWord_4189535 prefixEnd_4189535 2151245173834371158745185 := by
  unfold tailWord_4189535
  simp only [CollatzResearch.WordTrace]
  refine ⟨152804894877037685458002059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101869929918025123638668039 152804894877037685458002059)
  ·
    refine ⟨229207342315556528187003089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152804894877037685458002059 229207342315556528187003089)
    ·
      refine ⟨171905506736667396140252317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229207342315556528187003089 171905506736667396140252317)
      ·
        refine ⟨64464565026250273552594619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171905506736667396140252317 64464565026250273552594619)
        ·
          refine ⟨96696847539375410328891929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64464565026250273552594619 96696847539375410328891929)
          ·
            refine ⟨72522635654531557746668947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96696847539375410328891929 72522635654531557746668947)
            ·
              refine ⟨108783953481797336620003421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72522635654531557746668947 108783953481797336620003421)
              ·
                refine ⟨40793982555674001232501283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108783953481797336620003421 40793982555674001232501283)
                ·
                  refine ⟨61190973833511001848751925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40793982555674001232501283 61190973833511001848751925)
                  ·
                    refine ⟨5736653796891656423320493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61190973833511001848751925 5736653796891656423320493)
                    ·
                      refine ⟨2151245173834371158745185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5736653796891656423320493 2151245173834371158745185)
                      ·
                        rfl

theorem cell23_4189535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_4189535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189535 prefixEnd_4189535 := by exact prefixLift 4189535
  have htrace : WordTrace (prefixWord ++ tailWord_4189535) baseStart_4189535 baseEnd_4189535 := by
    simpa [prefixWord, tailWord_4189535, baseEnd_4189535] using wordTrace_append hprefix tailTrace_4189535
  have hstable : (prefixWord ++ tailWord_4189535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189535).length < 2 ^ (prefixWord ++ tailWord_4189535).sum := by decide
  have hdescent : baseEnd_4189535 < baseStart_4189535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189536 : List Nat := [2, 1, 1, 3, 4, 2, 1, 3, 2, 2, 2]
def baseStart_4189536 : Nat := 118140960795 + 4189536 * 2 ^ 59
def prefixEnd_4189536 : Nat := 4983230072969 + 3 ^ 40 * 4189536 * 2
def baseEnd_4189536 : Nat := 2151245687315025654832681

theorem tailTrace_4189536 : CollatzResearch.WordTrace tailWord_4189536 prefixEnd_4189536 2151245687315025654832681 := by
  unfold tailWord_4189536
  simp only [CollatzResearch.WordTrace]
  refine ⟨76402465675017031314394231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101869954233356041752525641 76402465675017031314394231)
  ·
    refine ⟨114603698512525546971591347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76402465675017031314394231 114603698512525546971591347)
    ·
      refine ⟨171905547768788320457387021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114603698512525546971591347 171905547768788320457387021)
      ·
        refine ⟨64464580413295620171520133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171905547768788320457387021 64464580413295620171520133)
        ·
          refine ⟨12087108827492928782160025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64464580413295620171520133 12087108827492928782160025)
          ·
            refine ⟨9065331620619696586620019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12087108827492928782160025 9065331620619696586620019)
            ·
              refine ⟨13597997430929544879930029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9065331620619696586620019 13597997430929544879930029)
              ·
                refine ⟨5099249036598579329973761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13597997430929544879930029 5099249036598579329973761)
                ·
                  refine ⟨3824436777448934497480321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5099249036598579329973761 3824436777448934497480321)
                  ·
                    refine ⟨2868327583086700873110241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3824436777448934497480321 2868327583086700873110241)
                    ·
                      refine ⟨2151245687315025654832681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2868327583086700873110241 2151245687315025654832681)
                      ·
                        rfl

theorem cell23_4189536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_4189536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189536 prefixEnd_4189536 := by exact prefixLift 4189536
  have htrace : WordTrace (prefixWord ++ tailWord_4189536) baseStart_4189536 baseEnd_4189536 := by
    simpa [prefixWord, tailWord_4189536, baseEnd_4189536] using wordTrace_append hprefix tailTrace_4189536
  have hstable : (prefixWord ++ tailWord_4189536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189536).length < 2 ^ (prefixWord ++ tailWord_4189536).sum := by decide
  have hdescent : baseEnd_4189536 < baseStart_4189536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189565 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_4189565 : Nat := 118140960795 + 4189565 * 2 ^ 59
def prefixEnd_4189565 : Nat := 4983230072969 + 3 ^ 40 * 4189565 * 2
def baseEnd_4189565 : Nat := 2151260578254006041370047

theorem tailTrace_4189565 : CollatzResearch.WordTrace tailWord_4189565 prefixEnd_4189565 2151260578254006041370047 := by
  unfold tailWord_4189565
  simp only [CollatzResearch.WordTrace]
  refine ⟨152805989066929000581594149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101870659377952667054396099 152805989066929000581594149)
  ·
    refine ⟨28651122950049187609048903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152805989066929000581594149 28651122950049187609048903)
    ·
      refine ⟨42976684425073781413573355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28651122950049187609048903 42976684425073781413573355)
      ·
        refine ⟨64465026637610672120360033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42976684425073781413573355 64465026637610672120360033)
        ·
          refine ⟨48348769978208004090270025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64465026637610672120360033 48348769978208004090270025)
          ·
            refine ⟨36261577483656003067702519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48348769978208004090270025 36261577483656003067702519)
            ·
              refine ⟨54392366225484004601553779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36261577483656003067702519 54392366225484004601553779)
              ·
                refine ⟨81588549338226006902330669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54392366225484004601553779 81588549338226006902330669)
                ·
                  refine ⟨30595706001834752588374001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81588549338226006902330669 30595706001834752588374001)
                  ·
                    refine ⟨22946779501376064441280501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30595706001834752588374001 22946779501376064441280501)
                    ·
                      refine ⟨2151260578254006041370047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22946779501376064441280501 2151260578254006041370047)
                      ·
                        rfl

theorem cell23_4189565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_4189565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189565 prefixEnd_4189565 := by exact prefixLift 4189565
  have htrace : WordTrace (prefixWord ++ tailWord_4189565) baseStart_4189565 baseEnd_4189565 := by
    simpa [prefixWord, tailWord_4189565, baseEnd_4189565] using wordTrace_append hprefix tailTrace_4189565
  have hstable : (prefixWord ++ tailWord_4189565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189565).length < 2 ^ (prefixWord ++ tailWord_4189565).sum := by decide
  have hdescent : baseEnd_4189565 < baseStart_4189565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189570 : List Nat := [3, 4, 2, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_4189570 : Nat := 118140960795 + 4189570 * 2 ^ 59
def prefixEnd_4189570 : Nat := 4983230072969 + 3 ^ 40 * 4189570 * 2
def baseEnd_4189570 : Nat := 2151263145657278521807525

theorem tailTrace_4189570 : CollatzResearch.WordTrace tailWord_4189570 prefixEnd_4189570 2151263145657278521807525 := by
  unfold tailWord_4189570
  simp only [CollatzResearch.WordTrace]
  refine ⟨38201542857977721608881541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101870780954607257623684109 38201542857977721608881541)
  ·
    refine ⟨7162789285870822801665289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38201542857977721608881541 7162789285870822801665289)
    ·
      refine ⟨5372091964403117101248967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7162789285870822801665289 5372091964403117101248967)
      ·
        refine ⟨8058137946604675651873451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5372091964403117101248967 8058137946604675651873451)
        ·
          refine ⟨12087206919907013477810177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8058137946604675651873451 12087206919907013477810177)
          ·
            refine ⟨9065405189930260108357633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12087206919907013477810177 9065405189930260108357633)
            ·
              refine ⟨6799053892447695081268225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9065405189930260108357633 6799053892447695081268225)
              ·
                refine ⟨5099290419335771310951169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6799053892447695081268225 5099290419335771310951169)
                ·
                  refine ⟨3824467814501828483213377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5099290419335771310951169 3824467814501828483213377)
                  ·
                    refine ⟨2868350860876371362410033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3824467814501828483213377 2868350860876371362410033)
                    ·
                      refine ⟨2151263145657278521807525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2868350860876371362410033 2151263145657278521807525)
                      ·
                        rfl

theorem cell23_4189570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_4189570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189570 prefixEnd_4189570 := by exact prefixLift 4189570
  have htrace : WordTrace (prefixWord ++ tailWord_4189570) baseStart_4189570 baseEnd_4189570 := by
    simpa [prefixWord, tailWord_4189570, baseEnd_4189570] using wordTrace_append hprefix tailTrace_4189570
  have hstable : (prefixWord ++ tailWord_4189570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189570).length < 2 ^ (prefixWord ++ tailWord_4189570).sum := by decide
  have hdescent : baseEnd_4189570 < baseStart_4189570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189572 : List Nat := [2, 3, 2, 1, 1, 3, 2, 2, 2, 5]
def baseStart_4189572 : Nat := 118140960795 + 4189572 * 2 ^ 59
def prefixEnd_4189572 : Nat := 4983230072969 + 3 ^ 40 * 4189572 * 2
def baseEnd_4189572 : Nat := 717088057539529171327505

theorem tailTrace_4189572 : CollatzResearch.WordTrace tailWord_4189572 prefixEnd_4189572 717088057539529171327505 := by
  unfold tailWord_4189572
  simp only [CollatzResearch.WordTrace]
  refine ⟨76403122188951820388549485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101870829585269093851399313 76403122188951820388549485)
  ·
    refine ⟨28651170820856932645706057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76403122188951820388549485 28651170820856932645706057)
    ·
      refine ⟨21488378115642699484279543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28651170820856932645706057 21488378115642699484279543)
      ·
        refine ⟨32232567173464049226419315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21488378115642699484279543 32232567173464049226419315)
        ·
          refine ⟨48348850760196073839628973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32232567173464049226419315 48348850760196073839628973)
          ·
            refine ⟨18130819035073527689860865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48348850760196073839628973 18130819035073527689860865)
            ·
              refine ⟨13598114276305145767395649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18130819035073527689860865 13598114276305145767395649)
              ·
                refine ⟨10198585707228859325546737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13598114276305145767395649 10198585707228859325546737)
                ·
                  refine ⟨7648939280421644494160053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10198585707228859325546737 7648939280421644494160053)
                  ·
                    refine ⟨717088057539529171327505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7648939280421644494160053 717088057539529171327505)
                    ·
                      rfl

theorem cell23_4189572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_4189572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189572 prefixEnd_4189572 := by exact prefixLift 4189572
  have htrace : WordTrace (prefixWord ++ tailWord_4189572) baseStart_4189572 baseEnd_4189572 := by
    simpa [prefixWord, tailWord_4189572, baseEnd_4189572] using wordTrace_append hprefix tailTrace_4189572
  have hstable : (prefixWord ++ tailWord_4189572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189572).length < 2 ^ (prefixWord ++ tailWord_4189572).sum := by decide
  have hdescent : baseEnd_4189572 < baseStart_4189572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189576 : List Nat := [2, 1, 3, 3, 1, 4, 2, 2, 5]
def baseStart_4189576 : Nat := 118140960795 + 4189576 * 2 ^ 59
def prefixEnd_4189576 : Nat := 4983230072969 + 3 ^ 40 * 4189576 * 2
def baseEnd_4189576 : Nat := 239029580726800610925833

theorem tailTrace_4189576 : CollatzResearch.WordTrace tailWord_4189576 prefixEnd_4189576 239029580726800610925833 := by
  unfold tailWord_4189576
  simp only [CollatzResearch.WordTrace]
  refine ⟨76403195134944574730122291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101870926846592766306829721 76403195134944574730122291)
  ·
    refine ⟨114604792702416862095183437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76403195134944574730122291 114604792702416862095183437)
    ·
      refine ⟨42976797263406323285693789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114604792702416862095183437 42976797263406323285693789)
      ·
        refine ⟨16116298973777371232135171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42976797263406323285693789 16116298973777371232135171)
        ·
          refine ⟨24174448460666056848202757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16116298973777371232135171 24174448460666056848202757)
          ·
            refine ⟨4532709086374885659038017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24174448460666056848202757 4532709086374885659038017)
            ·
              refine ⟨3399531814781164244278513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4532709086374885659038017 3399531814781164244278513)
              ·
                refine ⟨2549648861085873183208885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3399531814781164244278513 2549648861085873183208885)
                ·
                  refine ⟨239029580726800610925833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2549648861085873183208885 239029580726800610925833)
                  ·
                    rfl

theorem cell23_4189576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 5].length) (baseStart_4189576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189576 prefixEnd_4189576 := by exact prefixLift 4189576
  have htrace : WordTrace (prefixWord ++ tailWord_4189576) baseStart_4189576 baseEnd_4189576 := by
    simpa [prefixWord, tailWord_4189576, baseEnd_4189576] using wordTrace_append hprefix tailTrace_4189576
  have hstable : (prefixWord ++ tailWord_4189576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189576).length < 2 ^ (prefixWord ++ tailWord_4189576).sum := by decide
  have hdescent : baseEnd_4189576 < baseStart_4189576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189586 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_4189586 : Nat := 118140960795 + 4189586 * 2 ^ 59
def prefixEnd_4189586 : Nat := 4983230072969 + 3 ^ 40 * 4189586 * 2
def baseEnd_4189586 : Nat := 2151271361347750459207451

theorem tailTrace_4189586 : CollatzResearch.WordTrace tailWord_4189586 prefixEnd_4189586 2151271361347750459207451 := by
  unfold tailWord_4189586
  simp only [CollatzResearch.WordTrace]
  refine ⟨38201688749963230292027153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101871169999901947445405741 38201688749963230292027153)
  ·
    refine ⟨28651266562472422719020365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38201688749963230292027153 28651266562472422719020365)
    ·
      refine ⟨10744224960927158519632637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28651266562472422719020365 10744224960927158519632637)
      ·
        refine ⟨4029084360347684444862239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10744224960927158519632637 4029084360347684444862239)
        ·
          refine ⟨6043626540521526667293359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4029084360347684444862239 6043626540521526667293359)
          ·
            refine ⟨9065439810782290000940039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6043626540521526667293359 9065439810782290000940039)
            ·
              refine ⟨13598159716173435001410059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9065439810782290000940039 13598159716173435001410059)
              ·
                refine ⟨20397239574260152502115089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13598159716173435001410059 20397239574260152502115089)
                ·
                  refine ⟨15297929680695114376586317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20397239574260152502115089 15297929680695114376586317)
                  ·
                    refine ⟨5736723630260667891219869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15297929680695114376586317 5736723630260667891219869)
                    ·
                      refine ⟨2151271361347750459207451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5736723630260667891219869 2151271361347750459207451)
                      ·
                        rfl

theorem cell23_4189586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_4189586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189586 prefixEnd_4189586 := by exact prefixLift 4189586
  have htrace : WordTrace (prefixWord ++ tailWord_4189586) baseStart_4189586 baseEnd_4189586 := by
    simpa [prefixWord, tailWord_4189586, baseEnd_4189586] using wordTrace_append hprefix tailTrace_4189586
  have hstable : (prefixWord ++ tailWord_4189586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189586).length < 2 ^ (prefixWord ++ tailWord_4189586).sum := by decide
  have hdescent : baseEnd_4189586 < baseStart_4189586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189605 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 1, 6, 4]
def baseStart_4189605 : Nat := 118140960795 + 4189605 * 2 ^ 59
def prefixEnd_4189605 : Nat := 4983230072969 + 3 ^ 40 * 4189605 * 2
def baseEnd_4189605 : Nat := 2151281117480185884869863

theorem tailTrace_4189605 : CollatzResearch.WordTrace tailWord_4189605 prefixEnd_4189605 2151281117480185884869863 := by
  unfold tailWord_4189605
  simp only [CollatzResearch.WordTrace]
  refine ⟨152807447986784087413050269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101871631991189391608700179 152807447986784087413050269)
  ·
    refine ⟨57302792995044032779893851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152807447986784087413050269 57302792995044032779893851)
    ·
      refine ⟨85954189492566049169840777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57302792995044032779893851 85954189492566049169840777)
      ·
        refine ⟨64465642119424536877380583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85954189492566049169840777 64465642119424536877380583)
        ·
          refine ⟨96698463179136805316070875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64465642119424536877380583 96698463179136805316070875)
          ·
            refine ⟨145047694768705207974106313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96698463179136805316070875 145047694768705207974106313)
            ·
              refine ⟨108785771076528905980579735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145047694768705207974106313 108785771076528905980579735)
              ·
                refine ⟨163178656614793358970869603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108785771076528905980579735 163178656614793358970869603)
                ·
                  refine ⟨244767984922190038456304405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163178656614793358970869603 244767984922190038456304405)
                  ·
                    refine ⟨11473499293227658052639269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 244767984922190038456304405 11473499293227658052639269)
                    ·
                      refine ⟨2151281117480185884869863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11473499293227658052639269 2151281117480185884869863)
                      ·
                        rfl

theorem cell23_4189605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_4189605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189605 prefixEnd_4189605 := by exact prefixLift 4189605
  have htrace : WordTrace (prefixWord ++ tailWord_4189605) baseStart_4189605 baseEnd_4189605 := by
    simpa [prefixWord, tailWord_4189605, baseEnd_4189605] using wordTrace_append hprefix tailTrace_4189605
  have hstable : (prefixWord ++ tailWord_4189605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189605).length < 2 ^ (prefixWord ++ tailWord_4189605).sum := by decide
  have hdescent : baseEnd_4189605 < baseStart_4189605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189632 : List Nat := [2, 1, 1, 2, 3, 1, 5, 2, 6]
def baseStart_4189632 : Nat := 118140960795 + 4189632 * 2 ^ 59
def prefixEnd_4189632 : Nat := 4983230072969 + 3 ^ 40 * 4189632 * 2
def baseEnd_4189632 : Nat := 239032775717539697692471

theorem tailTrace_4189632 : CollatzResearch.WordTrace tailWord_4189632 prefixEnd_4189632 239032775717539697692471 := by
  unfold tailWord_4189632
  simp only [CollatzResearch.WordTrace]
  refine ⟨76404216378843135512141575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101872288505124180682855433 76404216378843135512141575)
  ·
    refine ⟨114606324568264703268212363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76404216378843135512141575 114606324568264703268212363)
    ·
      refine ⟨171909486852397054902318545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114606324568264703268212363 171909486852397054902318545)
      ·
        refine ⟨128932115139297791176738909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171909486852397054902318545 128932115139297791176738909)
        ·
          refine ⟨48349543177236671691277091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128932115139297791176738909 48349543177236671691277091)
          ·
            refine ⟨72524314765855007536915637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48349543177236671691277091 72524314765855007536915637)
            ·
              refine ⟨6799154509298906956585841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72524314765855007536915637 6799154509298906956585841)
              ·
                refine ⟨5099365881974180217439381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6799154509298906956585841 5099365881974180217439381)
                ·
                  refine ⟨239032775717539697692471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5099365881974180217439381 239032775717539697692471)
                  ·
                    rfl

theorem cell23_4189632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 6].length) (baseStart_4189632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189632 prefixEnd_4189632 := by exact prefixLift 4189632
  have htrace : WordTrace (prefixWord ++ tailWord_4189632) baseStart_4189632 baseEnd_4189632 := by
    simpa [prefixWord, tailWord_4189632, baseEnd_4189632] using wordTrace_append hprefix tailTrace_4189632
  have hstable : (prefixWord ++ tailWord_4189632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189632).length < 2 ^ (prefixWord ++ tailWord_4189632).sum := by decide
  have hdescent : baseEnd_4189632 < baseStart_4189632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189635 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 6]
def baseStart_4189635 : Nat := 118140960795 + 4189635 * 2 ^ 59
def prefixEnd_4189635 : Nat := 4983230072969 + 3 ^ 40 * 4189635 * 2
def baseEnd_4189635 : Nat := 2151296521899820767494725

theorem tailTrace_4189635 : CollatzResearch.WordTrace tailWord_4189635 prefixEnd_4189635 2151296521899820767494725 := by
  unfold tailWord_4189635
  simp only [CollatzResearch.WordTrace]
  refine ⟨152808542176675402536642359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101872361451116935024428239 152808542176675402536642359)
  ·
    refine ⟨229212813265013103804963539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152808542176675402536642359 229212813265013103804963539)
    ·
      refine ⟨343819219897519655707445309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229212813265013103804963539 343819219897519655707445309)
      ·
        refine ⟨128932207461569870890291991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343819219897519655707445309 128932207461569870890291991)
        ·
          refine ⟨193398311192354806335437987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128932207461569870890291991 193398311192354806335437987)
          ·
            refine ⟨290097466788532209503156981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193398311192354806335437987 290097466788532209503156981)
            ·
              refine ⟨27196637511424894640920967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 290097466788532209503156981 27196637511424894640920967)
              ·
                refine ⟨40794956267137341961381451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27196637511424894640920967 40794956267137341961381451)
                ·
                  refine ⟨61192434400706012942072177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40794956267137341961381451 61192434400706012942072177)
                  ·
                    refine ⟨45894325800529509706554133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61192434400706012942072177 45894325800529509706554133)
                    ·
                      refine ⟨2151296521899820767494725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45894325800529509706554133 2151296521899820767494725)
                      ·
                        rfl

theorem cell23_4189635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_4189635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189635 prefixEnd_4189635 := by exact prefixLift 4189635
  have htrace : WordTrace (prefixWord ++ tailWord_4189635) baseStart_4189635 baseEnd_4189635 := by
    simpa [prefixWord, tailWord_4189635, baseEnd_4189635] using wordTrace_append hprefix tailTrace_4189635
  have hstable : (prefixWord ++ tailWord_4189635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189635).length < 2 ^ (prefixWord ++ tailWord_4189635).sum := by decide
  have hdescent : baseEnd_4189635 < baseStart_4189635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189636 : List Nat := [2, 3, 3, 2, 1, 2, 2, 1, 3, 4]
def baseStart_4189636 : Nat := 118140960795 + 4189636 * 2 ^ 59
def prefixEnd_4189636 : Nat := 4983230072969 + 3 ^ 40 * 4189636 * 2
def baseEnd_4189636 : Nat := 717099011793491754527407

theorem tailTrace_4189636 : CollatzResearch.WordTrace tailWord_4189636 prefixEnd_4189636 717099011793491754527407 := by
  unfold tailWord_4189636
  simp only [CollatzResearch.WordTrace]
  refine ⟨76404289324835889853714381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101872385766447853138285841 76404289324835889853714381)
  ·
    refine ⟨28651608496813458695142893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76404289324835889853714381 28651608496813458695142893)
    ·
      refine ⟨10744353186305047010678585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28651608496813458695142893 10744353186305047010678585)
      ·
        refine ⟨8058264889728785258008939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10744353186305047010678585 8058264889728785258008939)
        ·
          refine ⟨12087397334593177887013409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8058264889728785258008939 12087397334593177887013409)
          ·
            refine ⟨9065548000944883415260057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12087397334593177887013409 9065548000944883415260057)
            ·
              refine ⟨6799161000708662561445043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9065548000944883415260057 6799161000708662561445043)
              ·
                refine ⟨10198741501062993842167565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6799161000708662561445043 10198741501062993842167565)
                ·
                  refine ⟨3824528062898622690812837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10198741501062993842167565 3824528062898622690812837)
                  ·
                    refine ⟨717099011793491754527407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3824528062898622690812837 717099011793491754527407)
                    ·
                      rfl

theorem cell23_4189636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_4189636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189636 prefixEnd_4189636 := by exact prefixLift 4189636
  have htrace : WordTrace (prefixWord ++ tailWord_4189636) baseStart_4189636 baseEnd_4189636 := by
    simpa [prefixWord, tailWord_4189636, baseEnd_4189636] using wordTrace_append hprefix tailTrace_4189636
  have hstable : (prefixWord ++ tailWord_4189636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189636).length < 2 ^ (prefixWord ++ tailWord_4189636).sum := by decide
  have hdescent : baseEnd_4189636 < baseStart_4189636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189655 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 7]
def baseStart_4189655 : Nat := 118140960795 + 4189655 * 2 ^ 59
def prefixEnd_4189655 : Nat := 4983230072969 + 3 ^ 40 * 4189655 * 2
def baseEnd_4189655 : Nat := 2151306791512910689244633

theorem tailTrace_4189655 : CollatzResearch.WordTrace tailWord_4189655 prefixEnd_4189655 2151306791512910689244633 := by
  unfold tailWord_4189655
  simp only [CollatzResearch.WordTrace]
  refine ⟨152809271636602945952370419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101872847757735297301580279 152809271636602945952370419)
  ·
    refine ⟨229213907454904418928555629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152809271636602945952370419 229213907454904418928555629)
    ·
      refine ⟨85955215295589157098208361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229213907454904418928555629 85955215295589157098208361)
      ·
        refine ⟨64466411471691867823656271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85955215295589157098208361 64466411471691867823656271)
        ·
          refine ⟨96699617207537801735484407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64466411471691867823656271 96699617207537801735484407)
          ·
            refine ⟨145049425811306702603226611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96699617207537801735484407 145049425811306702603226611)
            ·
              refine ⟨217574138716960053904839917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145049425811306702603226611 217574138716960053904839917)
              ·
                refine ⟨81590302018860020214314969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217574138716960053904839917 81590302018860020214314969)
                ·
                  refine ⟨61192726514145015160736227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81590302018860020214314969 61192726514145015160736227)
                  ·
                    refine ⟨91789089771217522741104341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61192726514145015160736227 91789089771217522741104341)
                    ·
                      refine ⟨2151306791512910689244633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91789089771217522741104341 2151306791512910689244633)
                      ·
                        rfl

theorem cell23_4189655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_4189655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189655 prefixEnd_4189655 := by exact prefixLift 4189655
  have htrace : WordTrace (prefixWord ++ tailWord_4189655) baseStart_4189655 baseEnd_4189655 := by
    simpa [prefixWord, tailWord_4189655, baseEnd_4189655] using wordTrace_append hprefix tailTrace_4189655
  have hstable : (prefixWord ++ tailWord_4189655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189655).length < 2 ^ (prefixWord ++ tailWord_4189655).sum := by decide
  have hdescent : baseEnd_4189655 < baseStart_4189655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189676 : List Nat := [2, 2, 1, 1, 2, 1, 2, 7, 1, 1, 3]
def baseStart_4189676 : Nat := 118140960795 + 4189676 * 2 ^ 59
def prefixEnd_4189676 : Nat := 4983230072969 + 3 ^ 40 * 4189676 * 2
def baseEnd_4189676 : Nat := 2151317574606655107082037

theorem tailTrace_4189676 : CollatzResearch.WordTrace tailWord_4189676 prefixEnd_4189676 2151317574606655107082037 := by
  unfold tailWord_4189676
  simp only [CollatzResearch.WordTrace]
  refine ⟨76405018784763433269442441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101873358379684577692589921 76405018784763433269442441)
  ·
    refine ⟨57303764088572574952081831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76405018784763433269442441 57303764088572574952081831)
    ·
      refine ⟨85955646132858862428122747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57303764088572574952081831 85955646132858862428122747)
      ·
        refine ⟨128933469199288293642184121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85955646132858862428122747 128933469199288293642184121)
        ·
          refine ⟨96700101899466220231638091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128933469199288293642184121 96700101899466220231638091)
          ·
            refine ⟨145050152849199330347457137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96700101899466220231638091 145050152849199330347457137)
            ·
              refine ⟨108787614636899497760592853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145050152849199330347457137 108787614636899497760592853)
              ·
                refine ⟨2549709718052331978763895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 108787614636899497760592853 2549709718052331978763895)
                ·
                  refine ⟨3824564577078497968145843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549709718052331978763895 3824564577078497968145843)
                  ·
                    refine ⟨5736846865617746952218765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3824564577078497968145843 5736846865617746952218765)
                    ·
                      refine ⟨2151317574606655107082037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5736846865617746952218765 2151317574606655107082037)
                      ·
                        rfl

theorem cell23_4189676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 1, 1, 3].length) (baseStart_4189676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189676 prefixEnd_4189676 := by exact prefixLift 4189676
  have htrace : WordTrace (prefixWord ++ tailWord_4189676) baseStart_4189676 baseEnd_4189676 := by
    simpa [prefixWord, tailWord_4189676, baseEnd_4189676] using wordTrace_append hprefix tailTrace_4189676
  have hstable : (prefixWord ++ tailWord_4189676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189676).length < 2 ^ (prefixWord ++ tailWord_4189676).sum := by decide
  have hdescent : baseEnd_4189676 < baseStart_4189676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189686 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2]
def baseStart_4189686 : Nat := 118140960795 + 4189686 * 2 ^ 59
def prefixEnd_4189686 : Nat := 4983230072969 + 3 ^ 40 * 4189686 * 2
def baseEnd_4189686 : Nat := 2151322709413200067956991

theorem tailTrace_4189686 : CollatzResearch.WordTrace tailWord_4189686 prefixEnd_4189686 2151322709413200067956991 := by
  unfold tailWord_4189686
  simp only [CollatzResearch.WordTrace]
  refine ⟨9550650143718164890421807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101873601532993758831165941 9550650143718164890421807)
  ·
    refine ⟨14325975215577247335632711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9550650143718164890421807 14325975215577247335632711)
    ·
      refine ⟨21488962823365871003449067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14325975215577247335632711 21488962823365871003449067)
      ·
        refine ⟨32233444235048806505173601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21488962823365871003449067 32233444235048806505173601)
        ·
          refine ⟨24175083176286604878880201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32233444235048806505173601 24175083176286604878880201)
          ·
            refine ⟨18131312382214953659160151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24175083176286604878880201 18131312382214953659160151)
            ·
              refine ⟨27196968573322430488740227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18131312382214953659160151 27196968573322430488740227)
              ·
                refine ⟨40795452859983645733110341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27196968573322430488740227 40795452859983645733110341)
                ·
                  refine ⟨7649147411246933574958189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40795452859983645733110341 7649147411246933574958189)
                  ·
                    refine ⟨2868430279217600090609321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7649147411246933574958189 2868430279217600090609321)
                    ·
                      refine ⟨2151322709413200067956991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2868430279217600090609321 2151322709413200067956991)
                      ·
                        rfl

theorem cell23_4189686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_4189686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189686 prefixEnd_4189686 := by exact prefixLift 4189686
  have htrace : WordTrace (prefixWord ++ tailWord_4189686) baseStart_4189686 baseEnd_4189686 := by
    simpa [prefixWord, tailWord_4189686, baseEnd_4189686] using wordTrace_append hprefix tailTrace_4189686
  have hstable : (prefixWord ++ tailWord_4189686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189686).length < 2 ^ (prefixWord ++ tailWord_4189686).sum := by decide
  have hdescent : baseEnd_4189686 < baseStart_4189686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189729 : List Nat := [1, 2, 3, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_4189729 : Nat := 118140960795 + 4189729 * 2 ^ 59
def prefixEnd_4189729 : Nat := 4983230072969 + 3 ^ 40 * 4189729 * 2
def baseEnd_4189729 : Nat := 2151344789081343399719293

theorem tailTrace_4189729 : CollatzResearch.WordTrace tailWord_4189729 prefixEnd_4189729 2151344789081343399719293 := by
  unfold tailWord_4189729
  simp only [CollatzResearch.WordTrace]
  refine ⟨152811970638334856590564241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101874647092223237727042827 152811970638334856590564241)
  ·
    refine ⟨114608977978751142442923181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152811970638334856590564241 114608977978751142442923181)
    ·
      refine ⟨42978366742031678416096193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114608977978751142442923181 42978366742031678416096193)
      ·
        refine ⟨32233775056523758812072145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42978366742031678416096193 32233775056523758812072145)
        ·
          refine ⟨24175331292392819109054109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32233775056523758812072145 24175331292392819109054109)
          ·
            refine ⟨9065749234647307165895291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24175331292392819109054109 9065749234647307165895291)
            ·
              refine ⟨13598623851970960748842937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9065749234647307165895291 13598623851970960748842937)
              ·
                refine ⟨10198967888978220561632203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13598623851970960748842937 10198967888978220561632203)
                ·
                  refine ⟨15298451833467330842448305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10198967888978220561632203 15298451833467330842448305)
                  ·
                    refine ⟨11473838875100498131836229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15298451833467330842448305 11473838875100498131836229)
                    ·
                      refine ⟨2151344789081343399719293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11473838875100498131836229 2151344789081343399719293)
                      ·
                        rfl

theorem cell23_4189729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_4189729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189729 prefixEnd_4189729 := by exact prefixLift 4189729
  have htrace : WordTrace (prefixWord ++ tailWord_4189729) baseStart_4189729 baseEnd_4189729 := by
    simpa [prefixWord, tailWord_4189729, baseEnd_4189729] using wordTrace_append hprefix tailTrace_4189729
  have hstable : (prefixWord ++ tailWord_4189729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189729).length < 2 ^ (prefixWord ++ tailWord_4189729).sum := by decide
  have hdescent : baseEnd_4189729 < baseStart_4189729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189733 : List Nat := [1, 3, 1, 2, 2, 1, 1, 7, 1, 2, 2]
def baseStart_4189733 : Nat := 118140960795 + 4189733 * 2 ^ 59
def prefixEnd_4189733 : Nat := 4983230072969 + 3 ^ 40 * 4189733 * 2
def baseEnd_4189733 : Nat := 2151346843003961384069275

theorem tailTrace_4189733 : CollatzResearch.WordTrace tailWord_4189733 prefixEnd_4189733 2151346843003961384069275 := by
  unfold tailWord_4189733
  simp only [CollatzResearch.WordTrace]
  refine ⟨152812116530320365273709853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101874744353546910182473235 152812116530320365273709853)
  ·
    refine ⟨57304543698870136977641195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152812116530320365273709853 57304543698870136977641195)
    ·
      refine ⟨85956815548305205466461793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57304543698870136977641195 85956815548305205466461793)
      ·
        refine ⟨64467611661228904099846345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85956815548305205466461793 64467611661228904099846345)
        ·
          refine ⟨48350708745921678074884759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64467611661228904099846345 48350708745921678074884759)
          ·
            refine ⟨72526063118882517112327139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48350708745921678074884759 72526063118882517112327139)
            ·
              refine ⟨108789094678323775668490709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72526063118882517112327139 108789094678323775668490709)
              ·
                refine ⟨2549744406523213492230251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 108789094678323775668490709 2549744406523213492230251)
                ·
                  refine ⟨3824616609784820238345377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549744406523213492230251 3824616609784820238345377)
                  ·
                    refine ⟨2868462457338615178759033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3824616609784820238345377 2868462457338615178759033)
                    ·
                      refine ⟨2151346843003961384069275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2868462457338615178759033 2151346843003961384069275)
                      ·
                        rfl

theorem cell23_4189733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_4189733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189733 prefixEnd_4189733 := by exact prefixLift 4189733
  have htrace : WordTrace (prefixWord ++ tailWord_4189733) baseStart_4189733 baseEnd_4189733 := by
    simpa [prefixWord, tailWord_4189733, baseEnd_4189733] using wordTrace_append hprefix tailTrace_4189733
  have hstable : (prefixWord ++ tailWord_4189733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189733).length < 2 ^ (prefixWord ++ tailWord_4189733).sum := by decide
  have hdescent : baseEnd_4189733 < baseStart_4189733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189752 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 2, 7]
def baseStart_4189752 : Nat := 118140960795 + 4189752 * 2 ^ 59
def prefixEnd_4189752 : Nat := 4983230072969 + 3 ^ 40 * 4189752 * 2
def baseEnd_4189752 : Nat := 717118866378798936577229

theorem tailTrace_4189752 : CollatzResearch.WordTrace tailWord_4189752 prefixEnd_4189752 717118866378798936577229 := by
  unfold tailWord_4189752
  simp only [CollatzResearch.WordTrace]
  refine ⟨76406404758625765759325755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101875206344834354345767673 76406404758625765759325755)
  ·
    refine ⟨114609607137938648638988633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76406404758625765759325755 114609607137938648638988633)
    ·
      refine ⟨85957205353453986479241475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114609607137938648638988633 85957205353453986479241475)
      ·
        refine ⟨128935808030180979718862213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85957205353453986479241475 128935808030180979718862213)
        ·
          refine ⟨24175464005658933697286665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128935808030180979718862213 24175464005658933697286665)
          ·
            refine ⟨18131598004244200272964999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24175464005658933697286665 18131598004244200272964999)
            ·
              refine ⟨27197397006366300409447499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18131598004244200272964999 27197397006366300409447499)
              ·
                refine ⟨40796095509549450614171249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27197397006366300409447499 40796095509549450614171249)
                ·
                  refine ⟨30597071632162087960628437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40796095509549450614171249 30597071632162087960628437)
                  ·
                    refine ⟨717118866378798936577229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30597071632162087960628437 717118866378798936577229)
                    ·
                      rfl

theorem cell23_4189752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_4189752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189752 prefixEnd_4189752 := by exact prefixLift 4189752
  have htrace : WordTrace (prefixWord ++ tailWord_4189752) baseStart_4189752 baseEnd_4189752 := by
    simpa [prefixWord, tailWord_4189752, baseEnd_4189752] using wordTrace_append hprefix tailTrace_4189752
  have hstable : (prefixWord ++ tailWord_4189752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189752).length < 2 ^ (prefixWord ++ tailWord_4189752).sum := by decide
  have hdescent : baseEnd_4189752 < baseStart_4189752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189756 : List Nat := [2, 2, 2, 2, 5, 1, 1, 8]
def baseStart_4189756 : Nat := 118140960795 + 4189756 * 2 ^ 59
def prefixEnd_4189756 : Nat := 4983230072969 + 3 ^ 40 * 4189756 * 2
def baseEnd_4189756 : Nat := 79679950113296844225247

theorem tailTrace_4189756 : CollatzResearch.WordTrace tailWord_4189756 prefixEnd_4189756 79679950113296844225247 := by
  unfold tailWord_4189756
  simp only [CollatzResearch.WordTrace]
  refine ⟨76406477704618520100898561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101875303606158026801198081 76406477704618520100898561)
  ·
    refine ⟨57304858278463890075673921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76406477704618520100898561 57304858278463890075673921)
    ·
      refine ⟨42978643708847917556755441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57304858278463890075673921 42978643708847917556755441)
      ·
        refine ⟨32233982781635938167566581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42978643708847917556755441 32233982781635938167566581)
        ·
          refine ⟨3021935885778369203209367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32233982781635938167566581 3021935885778369203209367)
          ·
            refine ⟨4532903828667553804814051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3021935885778369203209367 4532903828667553804814051)
            ·
              refine ⟨6799355743001330707221077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4532903828667553804814051 6799355743001330707221077)
              ·
                refine ⟨79679950113296844225247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6799355743001330707221077 79679950113296844225247)
                ·
                  rfl

theorem cell23_4189756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 8].length) (baseStart_4189756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189756 prefixEnd_4189756 := by exact prefixLift 4189756
  have htrace : WordTrace (prefixWord ++ tailWord_4189756) baseStart_4189756 baseEnd_4189756 := by
    simpa [prefixWord, tailWord_4189756, baseEnd_4189756] using wordTrace_append hprefix tailTrace_4189756
  have hstable : (prefixWord ++ tailWord_4189756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189756).length < 2 ^ (prefixWord ++ tailWord_4189756).sum := by decide
  have hdescent : baseEnd_4189756 < baseStart_4189756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189776 : List Nat := [2, 1, 1, 1, 1, 3, 4, 4, 1, 3, 2]
def baseStart_4189776 : Nat := 118140960795 + 4189776 * 2 ^ 59
def prefixEnd_4189776 : Nat := 4983230072969 + 3 ^ 40 * 4189776 * 2
def baseEnd_4189776 : Nat := 2151368922672104715831577

theorem tailTrace_4189776 : CollatzResearch.WordTrace tailWord_4189776 prefixEnd_4189776 2151368922672104715831577 := by
  unfold tailWord_4189776
  simp only [CollatzResearch.WordTrace]
  refine ⟨76406842434582291808762591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101875789912776389078350121 76406842434582291808762591)
  ·
    refine ⟨114610263651873437713143887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76406842434582291808762591 114610263651873437713143887)
    ·
      refine ⟨171915395477810156569715831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114610263651873437713143887 171915395477810156569715831)
      ·
        refine ⟨257873093216715234854573747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171915395477810156569715831 257873093216715234854573747)
        ·
          refine ⟨386809639825072852281860621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257873093216715234854573747 386809639825072852281860621)
          ·
            refine ⟨145053614934402319605697733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386809639825072852281860621 145053614934402319605697733)
            ·
              refine ⟨27197552800200434926068325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145053614934402319605697733 27197552800200434926068325)
              ·
                refine ⟨5099541150037581548637811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27197552800200434926068325 5099541150037581548637811)
                ·
                  refine ⟨7649311725056372322956717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5099541150037581548637811 7649311725056372322956717)
                  ·
                    refine ⟨2868491896896139621108769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7649311725056372322956717 2868491896896139621108769)
                    ·
                      refine ⟨2151368922672104715831577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2868491896896139621108769 2151368922672104715831577)
                      ·
                        rfl

theorem cell23_4189776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 1, 3, 2].length) (baseStart_4189776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189776 prefixEnd_4189776 := by exact prefixLift 4189776
  have htrace : WordTrace (prefixWord ++ tailWord_4189776) baseStart_4189776 baseEnd_4189776 := by
    simpa [prefixWord, tailWord_4189776, baseEnd_4189776] using wordTrace_append hprefix tailTrace_4189776
  have hstable : (prefixWord ++ tailWord_4189776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189776).length < 2 ^ (prefixWord ++ tailWord_4189776).sum := by decide
  have hdescent : baseEnd_4189776 < baseStart_4189776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189792 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 5]
def baseStart_4189792 : Nat := 118140960795 + 4189792 * 2 ^ 59
def prefixEnd_4189792 : Nat := 4983230072969 + 3 ^ 40 * 4189792 * 2
def baseEnd_4189792 : Nat := 2151377138362576653231503

theorem tailTrace_4189792 : CollatzResearch.WordTrace tailWord_4189792 prefixEnd_4189792 2151377138362576653231503 := by
  unfold tailWord_4189792
  simp only [CollatzResearch.WordTrace]
  refine ⟨76407134218553309175053815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101876178958071078900071753 76407134218553309175053815)
  ·
    refine ⟨114610701327829963762580723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76407134218553309175053815 114610701327829963762580723)
    ·
      refine ⟨171916051991744945643871085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114610701327829963762580723 171916051991744945643871085)
      ·
        refine ⟨64468519496904354616451657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171916051991744945643871085 64468519496904354616451657)
        ·
          refine ⟨48351389622678265962338743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64468519496904354616451657 48351389622678265962338743)
          ·
            refine ⟨72527084434017398943508115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48351389622678265962338743 72527084434017398943508115)
            ·
              refine ⟨108790626651026098415262173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72527084434017398943508115 108790626651026098415262173)
              ·
                refine ⟨40796484994134786905723315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108790626651026098415262173 40796484994134786905723315)
                ·
                  refine ⟨61194727491202180358584973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40796484994134786905723315 61194727491202180358584973)
                  ·
                    refine ⟨22948022809200817634469365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61194727491202180358584973 22948022809200817634469365)
                    ·
                      refine ⟨2151377138362576653231503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22948022809200817634469365 2151377138362576653231503)
                      ·
                        rfl

theorem cell23_4189792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_4189792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189792 prefixEnd_4189792 := by exact prefixLift 4189792
  have htrace : WordTrace (prefixWord ++ tailWord_4189792) baseStart_4189792 baseEnd_4189792 := by
    simpa [prefixWord, tailWord_4189792, baseEnd_4189792] using wordTrace_append hprefix tailTrace_4189792
  have hstable : (prefixWord ++ tailWord_4189792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189792).length < 2 ^ (prefixWord ++ tailWord_4189792).sum := by decide
  have hdescent : baseEnd_4189792 < baseStart_4189792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189800 : List Nat := [2, 1, 4, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_4189800 : Nat := 118140960795 + 4189800 * 2 ^ 59
def prefixEnd_4189800 : Nat := 4983230072969 + 3 ^ 40 * 4189800 * 2
def baseEnd_4189800 : Nat := 2151381246207812621931467

theorem tailTrace_4189800 : CollatzResearch.WordTrace tailWord_4189800 prefixEnd_4189800 2151381246207812621931467 := by
  unfold tailWord_4189800
  simp only [CollatzResearch.WordTrace]
  refine ⟨76407280110538817858199427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101876373480718423810932569 76407280110538817858199427)
  ·
    refine ⟨114610920165808226787299141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76407280110538817858199427 114610920165808226787299141)
    ·
      refine ⟨21489547531089042522618589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114610920165808226787299141 21489547531089042522618589)
      ·
        refine ⟨8058580324158390945981971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21489547531089042522618589 8058580324158390945981971)
        ·
          refine ⟨12087870486237586418972957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8058580324158390945981971 12087870486237586418972957)
          ·
            refine ⟨4532951432339094907114859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12087870486237586418972957 4532951432339094907114859)
            ·
              refine ⟨6799427148508642360672289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4532951432339094907114859 6799427148508642360672289)
              ·
                refine ⟨5099570361381481770504217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6799427148508642360672289 5099570361381481770504217)
                ·
                  refine ⟨3824677771036111327878163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5099570361381481770504217 3824677771036111327878163)
                  ·
                    refine ⟨5737016656554166991817245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3824677771036111327878163 5737016656554166991817245)
                    ·
                      refine ⟨2151381246207812621931467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5737016656554166991817245 2151381246207812621931467)
                      ·
                        rfl

theorem cell23_4189800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_4189800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189800 prefixEnd_4189800 := by exact prefixLift 4189800
  have htrace : WordTrace (prefixWord ++ tailWord_4189800) baseStart_4189800 baseEnd_4189800 := by
    simpa [prefixWord, tailWord_4189800, baseEnd_4189800] using wordTrace_append hprefix tailTrace_4189800
  have hstable : (prefixWord ++ tailWord_4189800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189800).length < 2 ^ (prefixWord ++ tailWord_4189800).sum := by decide
  have hdescent : baseEnd_4189800 < baseStart_4189800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189859 : List Nat := [1, 1, 1, 4, 1, 1, 5, 2, 2, 5]
def baseStart_4189859 : Nat := 118140960795 + 4189859 * 2 ^ 59
def prefixEnd_4189859 : Nat := 4983230072969 + 3 ^ 40 * 4189859 * 2
def baseEnd_4189859 : Nat := 717137180522142630364565

theorem tailTrace_4189859 : CollatzResearch.WordTrace tailWord_4189859 prefixEnd_4189859 717137180522142630364565 := by
  unfold tailWord_4189859
  simp only [CollatzResearch.WordTrace]
  refine ⟨152816712127863888792796631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101877808085242592528531087 152816712127863888792796631)
  ·
    refine ⟨229225068191795833189194947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152816712127863888792796631 229225068191795833189194947)
    ·
      refine ⟨343837602287693749783792421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229225068191795833189194947 343837602287693749783792421)
      ·
        refine ⟨64469550428942578084461079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343837602287693749783792421 64469550428942578084461079)
        ·
          refine ⟨96704325643413867126691619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64469550428942578084461079 96704325643413867126691619)
          ·
            refine ⟨145056488465120800690037429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96704325643413867126691619 145056488465120800690037429)
            ·
              refine ⟨13599045793605075064691009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145056488465120800690037429 13599045793605075064691009)
              ·
                refine ⟨10199284345203806298518257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13599045793605075064691009 10199284345203806298518257)
                ·
                  refine ⟨7649463258902854723888693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10199284345203806298518257 7649463258902854723888693)
                  ·
                    refine ⟨717137180522142630364565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7649463258902854723888693 717137180522142630364565)
                    ·
                      rfl

theorem cell23_4189859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 5].length) (baseStart_4189859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189859 prefixEnd_4189859 := by exact prefixLift 4189859
  have htrace : WordTrace (prefixWord ++ tailWord_4189859) baseStart_4189859 baseEnd_4189859 := by
    simpa [prefixWord, tailWord_4189859, baseEnd_4189859] using wordTrace_append hprefix tailTrace_4189859
  have hstable : (prefixWord ++ tailWord_4189859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189859).length < 2 ^ (prefixWord ++ tailWord_4189859).sum := by decide
  have hdescent : baseEnd_4189859 < baseStart_4189859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189896 : List Nat := [2, 1, 3, 1, 2, 2, 4, 1, 2, 1, 4]
def baseStart_4189896 : Nat := 118140960795 + 4189896 * 2 ^ 59
def prefixEnd_4189896 : Nat := 4983230072969 + 3 ^ 40 * 4189896 * 2
def baseEnd_4189896 : Nat := 2151430540350644246331025

theorem tailTrace_4189896 : CollatzResearch.WordTrace tailWord_4189896 prefixEnd_4189896 2151430540350644246331025 := by
  unfold tailWord_4189896
  simp only [CollatzResearch.WordTrace]
  refine ⟨76409030814364922055946771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101878707752486562741262361 76409030814364922055946771)
  ·
    refine ⟨114613546221547383083920157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76409030814364922055946771 114613546221547383083920157)
    ·
      refine ⟨42980079833080268656470059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114613546221547383083920157 42980079833080268656470059)
      ·
        refine ⟨64470119749620402984705089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42980079833080268656470059 64470119749620402984705089)
        ·
          refine ⟨48352589812215302238528817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64470119749620402984705089 48352589812215302238528817)
          ·
            refine ⟨36264442359161476678896613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48352589812215302238528817 36264442359161476678896613)
            ·
              refine ⟨6799582942342776877293115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36264442359161476678896613 6799582942342776877293115)
              ·
                refine ⟨10199374413514165315939673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6799582942342776877293115 10199374413514165315939673)
                ·
                  refine ⟨7649530810135623986954755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10199374413514165315939673 7649530810135623986954755)
                  ·
                    refine ⟨11474296215203435980432133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7649530810135623986954755 11474296215203435980432133)
                    ·
                      refine ⟨2151430540350644246331025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11474296215203435980432133 2151430540350644246331025)
                      ·
                        rfl

theorem cell23_4189896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_4189896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189896 prefixEnd_4189896 := by exact prefixLift 4189896
  have htrace : WordTrace (prefixWord ++ tailWord_4189896) baseStart_4189896 baseEnd_4189896 := by
    simpa [prefixWord, tailWord_4189896, baseEnd_4189896] using wordTrace_append hprefix tailTrace_4189896
  have hstable : (prefixWord ++ tailWord_4189896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189896).length < 2 ^ (prefixWord ++ tailWord_4189896).sum := by decide
  have hdescent : baseEnd_4189896 < baseStart_4189896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189899 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 3]
def baseStart_4189899 : Nat := 118140960795 + 4189899 * 2 ^ 59
def prefixEnd_4189899 : Nat := 4983230072969 + 3 ^ 40 * 4189899 * 2
def baseEnd_4189899 : Nat := 2151432080792607734593511

theorem tailTrace_4189899 : CollatzResearch.WordTrace tailWord_4189899 prefixEnd_4189899 2151432080792607734593511 := by
  unfold tailWord_4189899
  simp only [CollatzResearch.WordTrace]
  refine ⟨152818171047718975624252751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101878780698479317082835167 152818171047718975624252751)
  ·
    refine ⟨229227256571578463436379127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152818171047718975624252751 229227256571578463436379127)
    ·
      refine ⟨343840884857367695154568691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229227256571578463436379127 343840884857367695154568691)
      ·
        refine ⟨515761327286051542731853037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343840884857367695154568691 515761327286051542731853037)
        ·
          refine ⟨193410497732269328524444889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515761327286051542731853037 193410497732269328524444889)
          ·
            refine ⟨145057873299201996393333667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193410497732269328524444889 145057873299201996393333667)
            ·
              refine ⟨217586809948802994590000501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145057873299201996393333667 217586809948802994590000501)
              ·
                refine ⟨20398763432700280742812547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217586809948802994590000501 20398763432700280742812547)
                ·
                  refine ⟨30598145149050421114218821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20398763432700280742812547 30598145149050421114218821)
                  ·
                    refine ⟨5737152215446953958916029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30598145149050421114218821 5737152215446953958916029)
                    ·
                      refine ⟨2151432080792607734593511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5737152215446953958916029 2151432080792607734593511)
                      ·
                        rfl

theorem cell23_4189899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 3].length) (baseStart_4189899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189899 prefixEnd_4189899 := by exact prefixLift 4189899
  have htrace : WordTrace (prefixWord ++ tailWord_4189899) baseStart_4189899 baseEnd_4189899 := by
    simpa [prefixWord, tailWord_4189899, baseEnd_4189899] using wordTrace_append hprefix tailTrace_4189899
  have hstable : (prefixWord ++ tailWord_4189899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189899).length < 2 ^ (prefixWord ++ tailWord_4189899).sum := by decide
  have hdescent : baseEnd_4189899 < baseStart_4189899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189929 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 2, 5, 3]
def baseStart_4189929 : Nat := 118140960795 + 4189929 * 2 ^ 59
def prefixEnd_4189929 : Nat := 4983230072969 + 3 ^ 40 * 4189929 * 2
def baseEnd_4189929 : Nat := 2151447485212242617218373

theorem tailTrace_4189929 : CollatzResearch.WordTrace tailWord_4189929 prefixEnd_4189929 2151447485212242617218373 := by
  unfold tailWord_4189929
  simp only [CollatzResearch.WordTrace]
  refine ⟨152819265237610290747844841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101879510158406860498563227 152819265237610290747844841)
  ·
    refine ⟨114614448928207718060883631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152819265237610290747844841 114614448928207718060883631)
    ·
      refine ⟨171921673392311577091325447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114614448928207718060883631 171921673392311577091325447)
      ·
        refine ⟨257882510088467365636988171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171921673392311577091325447 257882510088467365636988171)
        ·
          refine ⟨386823765132701048455482257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257882510088467365636988171 386823765132701048455482257)
          ·
            refine ⟨290117823849525786341611693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386823765132701048455482257 290117823849525786341611693)
            ·
              refine ⟨108794183943572169878104385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290117823849525786341611693 108794183943572169878104385)
              ·
                refine ⟨81595637957679127408578289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108794183943572169878104385 81595637957679127408578289)
                ·
                  refine ⟨61196728468259345556433717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81595637957679127408578289 61196728468259345556433717)
                  ·
                    refine ⟨5737193293899313645915661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61196728468259345556433717 5737193293899313645915661)
                    ·
                      refine ⟨2151447485212242617218373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5737193293899313645915661 2151447485212242617218373)
                      ·
                        rfl

theorem cell23_4189929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 5, 3].length) (baseStart_4189929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189929 prefixEnd_4189929 := by exact prefixLift 4189929
  have htrace : WordTrace (prefixWord ++ tailWord_4189929) baseStart_4189929 baseEnd_4189929 := by
    simpa [prefixWord, tailWord_4189929, baseEnd_4189929] using wordTrace_append hprefix tailTrace_4189929
  have hstable : (prefixWord ++ tailWord_4189929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189929).length < 2 ^ (prefixWord ++ tailWord_4189929).sum := by decide
  have hdescent : baseEnd_4189929 < baseStart_4189929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189940 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_4189940 : Nat := 118140960795 + 4189940 * 2 ^ 59
def prefixEnd_4189940 : Nat := 4983230072969 + 3 ^ 40 * 4189940 * 2
def baseEnd_4189940 : Nat := 717151044499814024726941

theorem tailTrace_4189940 : CollatzResearch.WordTrace tailWord_4189940 prefixEnd_4189940 717151044499814024726941 := by
  unfold tailWord_4189940
  simp only [CollatzResearch.WordTrace]
  refine ⟨76409833220285219813247637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101879777627046959750996849 76409833220285219813247637)
  ·
    refine ⟨3581710932200869678745983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76409833220285219813247637 3581710932200869678745983)
    ·
      refine ⟨5372566398301304518118975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3581710932200869678745983 5372566398301304518118975)
      ·
        refine ⟨8058849597451956777178463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5372566398301304518118975 8058849597451956777178463)
        ·
          refine ⟨12088274396177935165767695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8058849597451956777178463 12088274396177935165767695)
          ·
            refine ⟨18132411594266902748651543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12088274396177935165767695 18132411594266902748651543)
            ·
              refine ⟨27198617391400354122977315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18132411594266902748651543 27198617391400354122977315)
              ·
                refine ⟨40797926087100531184465973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27198617391400354122977315 40797926087100531184465973)
                ·
                  refine ⟨3824805570665674798543685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40797926087100531184465973 3824805570665674798543685)
                  ·
                    refine ⟨717151044499814024726941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3824805570665674798543685 717151044499814024726941)
                    ·
                      rfl

theorem cell23_4189940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_4189940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189940 prefixEnd_4189940 := by exact prefixLift 4189940
  have htrace : WordTrace (prefixWord ++ tailWord_4189940) baseStart_4189940 baseEnd_4189940 := by
    simpa [prefixWord, tailWord_4189940, baseEnd_4189940] using wordTrace_append hprefix tailTrace_4189940
  have hstable : (prefixWord ++ tailWord_4189940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189940).length < 2 ^ (prefixWord ++ tailWord_4189940).sum := by decide
  have hdescent : baseEnd_4189940 < baseStart_4189940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189970 : List Nat := [3, 2, 4, 1, 1, 3, 1, 2, 6]
def baseStart_4189970 : Nat := 118140960795 + 4189970 * 2 ^ 59
def prefixEnd_4189970 : Nat := 4983230072969 + 3 ^ 40 * 4189970 * 2
def baseEnd_4189970 : Nat := 239052059768786328533965

theorem tailTrace_4189970 : CollatzResearch.WordTrace tailWord_4189970 prefixEnd_4189970 239052059768786328533965 := by
  unfold tailWord_4189970
  simp only [CollatzResearch.WordTrace]
  refine ⟨38205190157615438687521841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101880507086974503166724909 38205190157615438687521841)
  ·
    refine ⟨28653892618211579015641381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38205190157615438687521841 28653892618211579015641381)
    ·
      refine ⟨5372604865914671065432759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28653892618211579015641381 5372604865914671065432759)
      ·
        refine ⟨8058907298872006598149139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5372604865914671065432759 8058907298872006598149139)
        ·
          refine ⟨12088360948308009897223709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8058907298872006598149139 12088360948308009897223709)
          ·
            refine ⟨4533135355615503711458891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12088360948308009897223709 4533135355615503711458891)
            ·
              refine ⟨6799703033423255567188337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4533135355615503711458891 6799703033423255567188337)
              ·
                refine ⟨5099777275067441675391253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6799703033423255567188337 5099777275067441675391253)
                ·
                  refine ⟨239052059768786328533965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5099777275067441675391253 239052059768786328533965)
                  ·
                    rfl

theorem cell23_4189970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_4189970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189970 prefixEnd_4189970 := by exact prefixLift 4189970
  have htrace : WordTrace (prefixWord ++ tailWord_4189970) baseStart_4189970 baseEnd_4189970 := by
    simpa [prefixWord, tailWord_4189970, baseEnd_4189970] using wordTrace_append hprefix tailTrace_4189970
  have hstable : (prefixWord ++ tailWord_4189970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189970).length < 2 ^ (prefixWord ++ tailWord_4189970).sum := by decide
  have hdescent : baseEnd_4189970 < baseStart_4189970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189980 : List Nat := [2, 2, 3, 1, 1, 2, 1, 6, 1, 1, 3]
def baseStart_4189980 : Nat := 118140960795 + 4189980 * 2 ^ 59
def prefixEnd_4189980 : Nat := 4983230072969 + 3 ^ 40 * 4189980 * 2
def baseEnd_4189980 : Nat := 2151473672725621917680639

theorem tailTrace_4189980 : CollatzResearch.WordTrace tailWord_4189980 prefixEnd_4189980 2151473672725621917680639 := by
  unfold tailWord_4189980
  simp only [CollatzResearch.WordTrace]
  refine ⟨76410562680212763228975697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101880750240283684305300929 76410562680212763228975697)
  ·
    refine ⟨57307922010159572421731773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76410562680212763228975697 57307922010159572421731773)
    ·
      refine ⟨21490470753809839658149415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57307922010159572421731773 21490470753809839658149415)
      ·
        refine ⟨32235706130714759487224123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21490470753809839658149415 32235706130714759487224123)
        ·
          refine ⟨48353559196072139230836185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32235706130714759487224123 48353559196072139230836185)
          ·
            refine ⟨36265169397054104423127139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48353559196072139230836185 36265169397054104423127139)
            ·
              refine ⟨54397754095581156634690709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36265169397054104423127139 54397754095581156634690709)
              ·
                refine ⟨2549894723230366717251127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54397754095581156634690709 2549894723230366717251127)
                ·
                  refine ⟨3824842084845550075876691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549894723230366717251127 3824842084845550075876691)
                  ·
                    refine ⟨5737263127268325113815037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3824842084845550075876691 5737263127268325113815037)
                    ·
                      refine ⟨2151473672725621917680639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5737263127268325113815037 2151473672725621917680639)
                      ·
                        rfl

theorem cell23_4189980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_4189980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189980 prefixEnd_4189980 := by exact prefixLift 4189980
  have htrace : WordTrace (prefixWord ++ tailWord_4189980) baseStart_4189980 baseEnd_4189980 := by
    simpa [prefixWord, tailWord_4189980, baseEnd_4189980] using wordTrace_append hprefix tailTrace_4189980
  have hstable : (prefixWord ++ tailWord_4189980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189980).length < 2 ^ (prefixWord ++ tailWord_4189980).sum := by decide
  have hdescent : baseEnd_4189980 < baseStart_4189980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189996 : List Nat := [2, 2, 1, 1, 1, 5, 3, 1, 1, 6]
def baseStart_4189996 : Nat := 118140960795 + 4189996 * 2 ^ 59
def prefixEnd_4189996 : Nat := 4983230072969 + 3 ^ 40 * 4189996 * 2
def baseEnd_4189996 : Nat := 717160629472031285026855

theorem tailTrace_4189996 : CollatzResearch.WordTrace tailWord_4189996 prefixEnd_4189996 717160629472031285026855 := by
  unfold tailWord_4189996
  simp only [CollatzResearch.WordTrace]
  refine ⟨76410854464183780595266921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101881139285578374127022561 76410854464183780595266921)
  ·
    refine ⟨57308140848137835446450191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76410854464183780595266921 57308140848137835446450191)
    ·
      refine ⟨85962211272206753169675287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57308140848137835446450191 85962211272206753169675287)
      ·
        refine ⟨128943316908310129754512931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85962211272206753169675287 128943316908310129754512931)
        ·
          refine ⟨193414975362465194631769397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128943316908310129754512931 193414975362465194631769397)
          ·
            refine ⟨18132653940231111996728381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193414975362465194631769397 18132653940231111996728381)
            ·
              refine ⟨6799745227586666998773143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18132653940231111996728381 6799745227586666998773143)
              ·
                refine ⟨10199617841380000498159715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6799745227586666998773143 10199617841380000498159715)
                ·
                  refine ⟨15299426762070000747239573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10199617841380000498159715 15299426762070000747239573)
                  ·
                    refine ⟨717160629472031285026855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15299426762070000747239573 717160629472031285026855)
                    ·
                      rfl

theorem cell23_4189996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_4189996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189996 prefixEnd_4189996 := by exact prefixLift 4189996
  have htrace : WordTrace (prefixWord ++ tailWord_4189996) baseStart_4189996 baseEnd_4189996 := by
    simpa [prefixWord, tailWord_4189996, baseEnd_4189996] using wordTrace_append hprefix tailTrace_4189996
  have hstable : (prefixWord ++ tailWord_4189996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189996).length < 2 ^ (prefixWord ++ tailWord_4189996).sum := by decide
  have hdescent : baseEnd_4189996 < baseStart_4189996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189999 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 6]
def baseStart_4189999 : Nat := 118140960795 + 4189999 * 2 ^ 59
def prefixEnd_4189999 : Nat := 4983230072969 + 3 ^ 40 * 4189999 * 2
def baseEnd_4189999 : Nat := 2151483428858057343343051

theorem tailTrace_4189999 : CollatzResearch.WordTrace tailWord_4189999 prefixEnd_4189999 2151483428858057343343051 := by
  unfold tailWord_4189999
  simp only [CollatzResearch.WordTrace]
  refine ⟨152821818347356692702893051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101881212231571128468595367 152821818347356692702893051)
  ·
    refine ⟨229232727521035039054339577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152821818347356692702893051 229232727521035039054339577)
    ·
      refine ⟨171924545640776279290754683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229232727521035039054339577 171924545640776279290754683)
      ·
        refine ⟨257886818461164418936132025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171924545640776279290754683 257886818461164418936132025)
        ·
          refine ⟨193415113845873314202099019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257886818461164418936132025 193415113845873314202099019)
          ·
            refine ⟨290122670768809971303148529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193415113845873314202099019 290122670768809971303148529)
            ·
              refine ⟨217592003076607478477361397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290122670768809971303148529 217592003076607478477361397)
              ·
                refine ⟨20399250288431951107252631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217592003076607478477361397 20399250288431951107252631)
                ·
                  refine ⟨30598875432647926660878947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20399250288431951107252631 30598875432647926660878947)
                  ·
                    refine ⟨45898313148971889991318421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30598875432647926660878947 45898313148971889991318421)
                    ·
                      refine ⟨2151483428858057343343051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45898313148971889991318421 2151483428858057343343051)
                      ·
                        rfl

theorem cell23_4189999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_4189999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4189999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4189999 prefixEnd_4189999 := by exact prefixLift 4189999
  have htrace : WordTrace (prefixWord ++ tailWord_4189999) baseStart_4189999 baseEnd_4189999 := by
    simpa [prefixWord, tailWord_4189999, baseEnd_4189999] using wordTrace_append hprefix tailTrace_4189999
  have hstable : (prefixWord ++ tailWord_4189999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189999).length < 2 ^ (prefixWord ++ tailWord_4189999).sum := by decide
  have hdescent : baseEnd_4189999 < baseStart_4189999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190013 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 4, 4]
def baseStart_4190013 : Nat := 118140960795 + 4190013 * 2 ^ 59
def prefixEnd_4190013 : Nat := 4983230072969 + 3 ^ 40 * 4190013 * 2
def baseEnd_4190013 : Nat := 717163539195740096189329

theorem tailTrace_4190013 : CollatzResearch.WordTrace tailWord_4190013 prefixEnd_4190013 717163539195740096189329 := by
  unfold tailWord_4190013
  simp only [CollatzResearch.WordTrace]
  refine ⟨152822328969305973093902693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101881552646203982062601795 152822328969305973093902693)
  ·
    refine ⟨28654186681744869955106755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152822328969305973093902693 28654186681744869955106755)
    ·
      refine ⟨42981280022617304932660133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28654186681744869955106755 42981280022617304932660133)
      ·
        refine ⟨8058990004240744674873775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42981280022617304932660133 8058990004240744674873775)
        ·
          refine ⟨12088485006361117012310663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8058990004240744674873775 12088485006361117012310663)
          ·
            refine ⟨18132727509541675518465995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12088485006361117012310663 18132727509541675518465995)
            ·
              refine ⟨27199091264312513277698993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18132727509541675518465995 27199091264312513277698993)
              ·
                refine ⟨20399318448234384958274245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27199091264312513277698993 20399318448234384958274245)
                ·
                  refine ⟨3824872209043947179676421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20399318448234384958274245 3824872209043947179676421)
                  ·
                    refine ⟨717163539195740096189329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3824872209043947179676421 717163539195740096189329)
                    ·
                      rfl

theorem cell23_4190013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_4190013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190013 prefixEnd_4190013 := by exact prefixLift 4190013
  have htrace : WordTrace (prefixWord ++ tailWord_4190013) baseStart_4190013 baseEnd_4190013 := by
    simpa [prefixWord, tailWord_4190013, baseEnd_4190013] using wordTrace_append hprefix tailTrace_4190013
  have hstable : (prefixWord ++ tailWord_4190013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190013).length < 2 ^ (prefixWord ++ tailWord_4190013).sum := by decide
  have hdescent : baseEnd_4190013 < baseStart_4190013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190014 : List Nat := [4, 2, 1, 2, 2, 3, 1, 3, 1, 1, 3]
def baseStart_4190014 : Nat := 118140960795 + 4190014 * 2 ^ 59
def prefixEnd_4190014 : Nat := 4983230072969 + 3 ^ 40 * 4190014 * 2
def baseEnd_4190014 : Nat := 2151491131067874784655483

theorem tailTrace_4190014 : CollatzResearch.WordTrace tailWord_4190014 prefixEnd_4190014 2151491131067874784655483 := by
  unfold tailWord_4190014
  simp only [CollatzResearch.WordTrace]
  refine ⟨19102795680287793783086137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101881576961534900176459397 19102795680287793783086137)
  ·
    refine ⟨14327096760215845337314603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19102795680287793783086137 14327096760215845337314603)
    ·
      refine ⟨21490645140323768005971905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14327096760215845337314603 21490645140323768005971905)
      ·
        refine ⟨16117983855242826004478929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21490645140323768005971905 16117983855242826004478929)
        ·
          refine ⟨12088487891432119503359197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16117983855242826004478929 12088487891432119503359197)
          ·
            refine ⟨4533182959287044813759699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12088487891432119503359197 4533182959287044813759699)
            ·
              refine ⟨6799774438930567220639549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4533182959287044813759699 6799774438930567220639549)
              ·
                refine ⟨2549915414598962707739831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6799774438930567220639549 2549915414598962707739831)
                ·
                  refine ⟨3824873121898444061609747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549915414598962707739831 3824873121898444061609747)
                  ·
                    refine ⟨5737309682847666092414621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3824873121898444061609747 5737309682847666092414621)
                    ·
                      refine ⟨2151491131067874784655483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5737309682847666092414621 2151491131067874784655483)
                      ·
                        rfl

theorem cell23_4190014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_4190014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190014 prefixEnd_4190014 := by exact prefixLift 4190014
  have htrace : WordTrace (prefixWord ++ tailWord_4190014) baseStart_4190014 baseEnd_4190014 := by
    simpa [prefixWord, tailWord_4190014, baseEnd_4190014] using wordTrace_append hprefix tailTrace_4190014
  have hstable : (prefixWord ++ tailWord_4190014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190014).length < 2 ^ (prefixWord ++ tailWord_4190014).sum := by decide
  have hdescent : baseEnd_4190014 < baseStart_4190014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190023 : List Nat := [1, 1, 4, 1, 2, 1, 4, 3, 1, 2, 3]
def baseStart_4190023 : Nat := 118140960795 + 4190023 * 2 ^ 59
def prefixEnd_4190023 : Nat := 4983230072969 + 3 ^ 40 * 4190023 * 2
def baseEnd_4190023 : Nat := 2151495752393765249442941

theorem tailTrace_4190023 : CollatzResearch.WordTrace tailWord_4190023 prefixEnd_4190023 2151495752393765249442941 := by
  unfold tailWord_4190023
  simp only [CollatzResearch.WordTrace]
  refine ⟨152822693699269744801766723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101881795799513163201177815 152822693699269744801766723)
  ·
    refine ⟨229234040548904617202650085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152822693699269744801766723 229234040548904617202650085)
    ·
      refine ⟨42981382602919615725496891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229234040548904617202650085 42981382602919615725496891)
      ·
        refine ⟨64472073904379423588245337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42981382602919615725496891 64472073904379423588245337)
        ·
          refine ⟨48354055428284567691184003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64472073904379423588245337 48354055428284567691184003)
          ·
            refine ⟨72531083142426851536776005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48354055428284567691184003 72531083142426851536776005)
            ·
              refine ⟨13599578089205034663145501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72531083142426851536776005 13599578089205034663145501)
              ·
                refine ⟨5099841783451887998679563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13599578089205034663145501 5099841783451887998679563)
                ·
                  refine ⟨7649762675177831998019345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5099841783451887998679563 7649762675177831998019345)
                  ·
                    refine ⟨5737322006383373998514509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7649762675177831998019345 5737322006383373998514509)
                    ·
                      refine ⟨2151495752393765249442941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5737322006383373998514509 2151495752393765249442941)
                      ·
                        rfl

theorem cell23_4190023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_4190023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190023 prefixEnd_4190023 := by exact prefixLift 4190023
  have htrace : WordTrace (prefixWord ++ tailWord_4190023) baseStart_4190023 baseEnd_4190023 := by
    simpa [prefixWord, tailWord_4190023, baseEnd_4190023] using wordTrace_append hprefix tailTrace_4190023
  have hstable : (prefixWord ++ tailWord_4190023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190023).length < 2 ^ (prefixWord ++ tailWord_4190023).sum := by decide
  have hdescent : baseEnd_4190023 < baseStart_4190023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190037 : List Nat := [1, 3, 2, 2, 2, 4, 1, 1, 3, 2, 2]
def baseStart_4190037 : Nat := 118140960795 + 4190037 * 2 ^ 59
def prefixEnd_4190037 : Nat := 4983230072969 + 3 ^ 40 * 4190037 * 2
def baseEnd_4190037 : Nat := 2151502941122928194667877

theorem tailTrace_4190037 : CollatzResearch.WordTrace tailWord_4190037 prefixEnd_4190037 2151502941122928194667877 := by
  unfold tailWord_4190037
  simp only [CollatzResearch.WordTrace]
  refine ⟨152823204321219025192776365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101882136214146016795184243 152823204321219025192776365)
  ·
    refine ⟨57308701620457134447291137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152823204321219025192776365 57308701620457134447291137)
    ·
      refine ⟨42981526215342850835468353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57308701620457134447291137 42981526215342850835468353)
      ·
        refine ⟨32236144661507138126601265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42981526215342850835468353 32236144661507138126601265)
        ·
          refine ⟨24177108496130353594950949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32236144661507138126601265 24177108496130353594950949)
          ·
            refine ⟨4533207843024441299053303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24177108496130353594950949 4533207843024441299053303)
            ·
              refine ⟨6799811764536661948579955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4533207843024441299053303 6799811764536661948579955)
              ·
                refine ⟨10199717646804992922869933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6799811764536661948579955 10199717646804992922869933)
                ·
                  refine ⟨3824894117551872346076225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10199717646804992922869933 3824894117551872346076225)
                  ·
                    refine ⟨2868670588163904259557169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3824894117551872346076225 2868670588163904259557169)
                    ·
                      refine ⟨2151502941122928194667877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2868670588163904259557169 2151502941122928194667877)
                      ·
                        rfl

theorem cell23_4190037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_4190037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190037 prefixEnd_4190037 := by exact prefixLift 4190037
  have htrace : WordTrace (prefixWord ++ tailWord_4190037) baseStart_4190037 baseEnd_4190037 := by
    simpa [prefixWord, tailWord_4190037, baseEnd_4190037] using wordTrace_append hprefix tailTrace_4190037
  have hstable : (prefixWord ++ tailWord_4190037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190037).length < 2 ^ (prefixWord ++ tailWord_4190037).sum := by decide
  have hdescent : baseEnd_4190037 < baseStart_4190037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190059 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 8]
def baseStart_4190059 : Nat := 118140960795 + 4190059 * 2 ^ 59
def prefixEnd_4190059 : Nat := 4983230072969 + 3 ^ 40 * 4190059 * 2
def baseEnd_4190059 : Nat := 2151514237697327108592775

theorem tailTrace_4190059 : CollatzResearch.WordTrace tailWord_4190059 prefixEnd_4190059 2151514237697327108592775 := by
  unfold tailWord_4190059
  simp only [CollatzResearch.WordTrace]
  refine ⟨152824006727139322950077231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101882671151426215300051487 152824006727139322950077231)
  ·
    refine ⟨229236010090708984425115847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152824006727139322950077231 229236010090708984425115847)
    ·
      refine ⟨343854015136063476637673771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229236010090708984425115847 343854015136063476637673771)
      ·
        refine ⟨515781022704095214956510657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343854015136063476637673771 515781022704095214956510657)
        ·
          refine ⟨386835767028071411217382993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515781022704095214956510657 386835767028071411217382993)
          ·
            refine ⟨290126825271053558413037245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386835767028071411217382993 290126825271053558413037245)
            ·
              refine ⟨108797559476645084404888967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290126825271053558413037245 108797559476645084404888967)
              ·
                refine ⟨163196339214967626607333451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108797559476645084404888967 163196339214967626607333451)
                ·
                  refine ⟨244794508822451439911000177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163196339214967626607333451 244794508822451439911000177)
                  ·
                    refine ⟨183595881616838579933250133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 244794508822451439911000177 183595881616838579933250133)
                    ·
                      refine ⟨2151514237697327108592775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 183595881616838579933250133 2151514237697327108592775)
                      ·
                        rfl

theorem cell23_4190059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 8].length) (baseStart_4190059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190059 prefixEnd_4190059 := by exact prefixLift 4190059
  have htrace : WordTrace (prefixWord ++ tailWord_4190059) baseStart_4190059 baseEnd_4190059 := by
    simpa [prefixWord, tailWord_4190059, baseEnd_4190059] using wordTrace_append hprefix tailTrace_4190059
  have hstable : (prefixWord ++ tailWord_4190059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190059).length < 2 ^ (prefixWord ++ tailWord_4190059).sum := by decide
  have hdescent : baseEnd_4190059 < baseStart_4190059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190087 : List Nat := [1, 1, 4, 2, 4, 1, 2, 2, 2, 1, 3]
def baseStart_4190087 : Nat := 118140960795 + 4190087 * 2 ^ 59
def prefixEnd_4190087 : Nat := 4983230072969 + 3 ^ 40 * 4190087 * 2
def baseEnd_4190087 : Nat := 2151528615155652999042647

theorem tailTrace_4190087 : CollatzResearch.WordTrace tailWord_4190087 prefixEnd_4190087 2151528615155652999042647 := by
  unfold tailWord_4190087
  simp only [CollatzResearch.WordTrace]
  refine ⟨152825027971037883732096515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101883351980691922488064343 152825027971037883732096515)
  ·
    refine ⟨229237541956556825598144773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152825027971037883732096515 229237541956556825598144773)
    ·
      refine ⟨42982039116854404799652145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229237541956556825598144773 42982039116854404799652145)
      ·
        refine ⟨32236529337640803599739109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42982039116854404799652145 32236529337640803599739109)
        ·
          refine ⟨6044349250807650674951083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32236529337640803599739109 6044349250807650674951083)
          ·
            refine ⟨9066523876211476012426625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6044349250807650674951083 9066523876211476012426625)
            ·
              refine ⟨6799892907158607009319969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9066523876211476012426625 6799892907158607009319969)
              ·
                refine ⟨5099919680368955256989977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6799892907158607009319969 5099919680368955256989977)
                ·
                  refine ⟨3824939760276716442742483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5099919680368955256989977 3824939760276716442742483)
                  ·
                    refine ⟨5737409640415074664113725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3824939760276716442742483 5737409640415074664113725)
                    ·
                      refine ⟨2151528615155652999042647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5737409640415074664113725 2151528615155652999042647)
                      ·
                        rfl

theorem cell23_4190087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_4190087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190087 prefixEnd_4190087 := by exact prefixLift 4190087
  have htrace : WordTrace (prefixWord ++ tailWord_4190087) baseStart_4190087 baseEnd_4190087 := by
    simpa [prefixWord, tailWord_4190087, baseEnd_4190087] using wordTrace_append hprefix tailTrace_4190087
  have hstable : (prefixWord ++ tailWord_4190087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190087).length < 2 ^ (prefixWord ++ tailWord_4190087).sum := by decide
  have hdescent : baseEnd_4190087 < baseStart_4190087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190088 : List Nat := [2, 1, 3, 3, 4, 1, 2, 2, 1, 2, 2]
def baseStart_4190088 : Nat := 118140960795 + 4190088 * 2 ^ 59
def prefixEnd_4190088 : Nat := 4983230072969 + 3 ^ 40 * 4190088 * 2
def baseEnd_4190088 : Nat := 2151529128636307495130143

theorem tailTrace_4190088 : CollatzResearch.WordTrace tailWord_4190088 prefixEnd_4190088 2151529128636307495130143 := by
  unfold tailWord_4190088
  simp only [CollatzResearch.WordTrace]
  refine ⟨76412532222017130451441459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101883376296022840601921945 76412532222017130451441459)
  ·
    refine ⟨114618798333025695677162189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76412532222017130451441459 114618798333025695677162189)
    ·
      refine ⟨42982049374884635878935821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114618798333025695677162189 42982049374884635878935821)
      ·
        refine ⟨16118268515581738454600933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42982049374884635878935821 16118268515581738454600933)
        ·
          refine ⟨3022175346671575960237675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16118268515581738454600933 3022175346671575960237675)
          ·
            refine ⟨4533263020007363940356513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022175346671575960237675 4533263020007363940356513)
            ·
              refine ⟨3399947265005522955267385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4533263020007363940356513 3399947265005522955267385)
              ·
                refine ⟨2549960448754142216450539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3399947265005522955267385 2549960448754142216450539)
                ·
                  refine ⟨3824940673131213324675809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549960448754142216450539 3824940673131213324675809)
                  ·
                    refine ⟨2868705504848409993506857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3824940673131213324675809 2868705504848409993506857)
                    ·
                      refine ⟨2151529128636307495130143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2868705504848409993506857 2151529128636307495130143)
                      ·
                        rfl

theorem cell23_4190088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_4190088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190088 prefixEnd_4190088 := by exact prefixLift 4190088
  have htrace : WordTrace (prefixWord ++ tailWord_4190088) baseStart_4190088 baseEnd_4190088 := by
    simpa [prefixWord, tailWord_4190088, baseEnd_4190088] using wordTrace_append hprefix tailTrace_4190088
  have hstable : (prefixWord ++ tailWord_4190088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190088).length < 2 ^ (prefixWord ++ tailWord_4190088).sum := by decide
  have hdescent : baseEnd_4190088 < baseStart_4190088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190096 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 3]
def baseStart_4190096 : Nat := 118140960795 + 4190096 * 2 ^ 59
def prefixEnd_4190096 : Nat := 4983230072969 + 3 ^ 40 * 4190096 * 2
def baseEnd_4190096 : Nat := 2151533236481543463830105

theorem tailTrace_4190096 : CollatzResearch.WordTrace tailWord_4190096 prefixEnd_4190096 2151533236481543463830105 := by
  unfold tailWord_4190096
  simp only [CollatzResearch.WordTrace]
  refine ⟨76412678114002639134587071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101883570818670185512782761 76412678114002639134587071)
  ·
    refine ⟨114619017171003958701880607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76412678114002639134587071 114619017171003958701880607)
    ·
      refine ⟨171928525756505938052820911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114619017171003958701880607 171928525756505938052820911)
      ·
        refine ⟨257892788634758907079231367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171928525756505938052820911 257892788634758907079231367)
        ·
          refine ⟨386839182952138360618847051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257892788634758907079231367 386839182952138360618847051)
          ·
            refine ⟨580258774428207540928270577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386839182952138360618847051 580258774428207540928270577)
            ·
              refine ⟨435194080821155655696202933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 580258774428207540928270577 435194080821155655696202933)
              ·
                refine ⟨40799445076983342721519025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 435194080821155655696202933 40799445076983342721519025)
                ·
                  refine ⟨30599583807737507041139269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40799445076983342721519025 30599583807737507041139269)
                  ·
                    refine ⟨5737421963950782570213613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30599583807737507041139269 5737421963950782570213613)
                    ·
                      refine ⟨2151533236481543463830105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5737421963950782570213613 2151533236481543463830105)
                      ·
                        rfl

theorem cell23_4190096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 3].length) (baseStart_4190096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190096 prefixEnd_4190096 := by exact prefixLift 4190096
  have htrace : WordTrace (prefixWord ++ tailWord_4190096) baseStart_4190096 baseEnd_4190096 := by
    simpa [prefixWord, tailWord_4190096, baseEnd_4190096] using wordTrace_append hprefix tailTrace_4190096
  have hstable : (prefixWord ++ tailWord_4190096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190096).length < 2 ^ (prefixWord ++ tailWord_4190096).sum := by decide
  have hdescent : baseEnd_4190096 < baseStart_4190096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190116 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 9]
def baseStart_4190116 : Nat := 118140960795 + 4190116 * 2 ^ 59
def prefixEnd_4190116 : Nat := 4983230072969 + 3 ^ 40 * 4190116 * 2
def baseEnd_4190116 : Nat := 239060389566070376175557

theorem tailTrace_4190116 : CollatzResearch.WordTrace tailWord_4190116 prefixEnd_4190116 239060389566070376175557 := by
  unfold tailWord_4190116
  simp only [CollatzResearch.WordTrace]
  refine ⟨76413042843966410842451101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101884057125288547789934801 76413042843966410842451101)
  ·
    refine ⟨28654891066487404065919163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76413042843966410842451101 28654891066487404065919163)
    ·
      refine ⟨42982336599731106098878745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28654891066487404065919163 42982336599731106098878745)
      ·
        refine ⟨32236752449798329574159059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42982336599731106098878745 32236752449798329574159059)
        ·
          refine ⟨48355128674697494361238589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32236752449798329574159059 48355128674697494361238589)
          ·
            refine ⟨18133173253011560385464471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48355128674697494361238589 18133173253011560385464471)
            ·
              refine ⟨27199759879517340578196707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18133173253011560385464471 27199759879517340578196707)
              ·
                refine ⟨40799639819276010867295061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27199759879517340578196707 40799639819276010867295061)
                ·
                  refine ⟨239060389566070376175557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40799639819276010867295061 239060389566070376175557)
                  ·
                    rfl

theorem cell23_4190116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_4190116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190116 prefixEnd_4190116 := by exact prefixLift 4190116
  have htrace : WordTrace (prefixWord ++ tailWord_4190116) baseStart_4190116 baseEnd_4190116 := by
    simpa [prefixWord, tailWord_4190116, baseEnd_4190116] using wordTrace_append hprefix tailTrace_4190116
  have hstable : (prefixWord ++ tailWord_4190116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190116).length < 2 ^ (prefixWord ++ tailWord_4190116).sum := by decide
  have hdescent : baseEnd_4190116 < baseStart_4190116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190203 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 3]
def baseStart_4190203 : Nat := 118140960795 + 4190203 * 2 ^ 59
def prefixEnd_4190203 : Nat := 4983230072969 + 3 ^ 40 * 4190203 * 2
def baseEnd_4190203 : Nat := 2151588178911574545192113

theorem tailTrace_4190203 : CollatzResearch.WordTrace tailWord_4190203 prefixEnd_4190203 2151588178911574545192113 := by
  unfold tailWord_4190203
  simp only [CollatzResearch.WordTrace]
  refine ⟨152829258838617635543319263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101886172559078423695546175 152829258838617635543319263)
  ·
    refine ⟨229243888257926453314978895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152829258838617635543319263 229243888257926453314978895)
    ·
      refine ⟨343865832386889679972468343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229243888257926453314978895 343865832386889679972468343)
      ·
        refine ⟨515798748580334519958702515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343865832386889679972468343 515798748580334519958702515)
        ·
          refine ⟨773698122870501779938053773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515798748580334519958702515 773698122870501779938053773)
          ·
            refine ⟨290136796076438167476770165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 773698122870501779938053773 290136796076438167476770165)
            ·
              refine ⟨27200324632166078200947203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 290136796076438167476770165 27200324632166078200947203)
              ·
                refine ⟨40800486948249117301420805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27200324632166078200947203 40800486948249117301420805)
                ·
                  refine ⟨7650091302796709494016401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40800486948249117301420805 7650091302796709494016401)
                  ·
                    refine ⟨5737568477097532120512301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7650091302796709494016401 5737568477097532120512301)
                    ·
                      refine ⟨2151588178911574545192113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5737568477097532120512301 2151588178911574545192113)
                      ·
                        rfl

theorem cell23_4190203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 3].length) (baseStart_4190203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190203 prefixEnd_4190203 := by exact prefixLift 4190203
  have htrace : WordTrace (prefixWord ++ tailWord_4190203) baseStart_4190203 baseEnd_4190203 := by
    simpa [prefixWord, tailWord_4190203, baseEnd_4190203] using wordTrace_append hprefix tailTrace_4190203
  have hstable : (prefixWord ++ tailWord_4190203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190203).length < 2 ^ (prefixWord ++ tailWord_4190203).sum := by decide
  have hdescent : baseEnd_4190203 < baseStart_4190203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190237 : List Nat := [1, 4, 2, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_4190237 : Nat := 118140960795 + 4190237 * 2 ^ 59
def prefixEnd_4190237 : Nat := 4983230072969 + 3 ^ 40 * 4190237 * 2
def baseEnd_4190237 : Nat := 2151605637253827412166957

theorem tailTrace_4190237 : CollatzResearch.WordTrace tailWord_4190237 prefixEnd_4190237 2151605637253827412166957 := by
  unfold tailWord_4190237
  simp only [CollatzResearch.WordTrace]
  refine ⟨152830498920494459350056965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101886999280329639566704643 152830498920494459350056965)
  ·
    refine ⟨28655718547592711128135681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152830498920494459350056965 28655718547592711128135681)
    ·
      refine ⟨21491788910694533346101761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28655718547592711128135681 21491788910694533346101761)
      ·
        refine ⟨16118841683020900009576321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21491788910694533346101761 16118841683020900009576321)
        ·
          refine ⟨12089131262265675007182241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16118841683020900009576321 12089131262265675007182241)
          ·
            refine ⟨9066848446699256255386681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12089131262265675007182241 9066848446699256255386681)
            ·
              refine ⟨6800136335024442191540011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9066848446699256255386681 6800136335024442191540011)
              ·
                refine ⟨10200204502536663287310017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6800136335024442191540011 10200204502536663287310017)
                ·
                  refine ⟨7650153376902497465482513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10200204502536663287310017 7650153376902497465482513)
                  ·
                    refine ⟨5737615032676873099111885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7650153376902497465482513 5737615032676873099111885)
                    ·
                      refine ⟨2151605637253827412166957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5737615032676873099111885 2151605637253827412166957)
                      ·
                        rfl

theorem cell23_4190237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_4190237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190237 prefixEnd_4190237 := by exact prefixLift 4190237
  have htrace : WordTrace (prefixWord ++ tailWord_4190237) baseStart_4190237 baseEnd_4190237 := by
    simpa [prefixWord, tailWord_4190237, baseEnd_4190237] using wordTrace_append hprefix tailTrace_4190237
  have hstable : (prefixWord ++ tailWord_4190237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190237).length < 2 ^ (prefixWord ++ tailWord_4190237).sum := by decide
  have hdescent : baseEnd_4190237 < baseStart_4190237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190267 : List Nat := [1, 1, 1, 1, 1, 2, 1, 10, 1, 1, 3]
def baseStart_4190267 : Nat := 118140960795 + 4190267 * 2 ^ 59
def prefixEnd_4190267 : Nat := 4983230072969 + 3 ^ 40 * 4190267 * 2
def baseEnd_4190267 : Nat := 2151621041673462294791819

theorem tailTrace_4190267 : CollatzResearch.WordTrace tailWord_4190267 prefixEnd_4190267 2151621041673462294791819 := by
  unfold tailWord_4190267
  simp only [CollatzResearch.WordTrace]
  refine ⟨152831593110385774473649055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101887728740257182982432703 152831593110385774473649055)
  ·
    refine ⟨229247389665578661710473583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152831593110385774473649055 229247389665578661710473583)
    ·
      refine ⟨343871084498367992565710375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229247389665578661710473583 343871084498367992565710375)
      ·
        refine ⟨515806626747551988848565563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343871084498367992565710375 515806626747551988848565563)
        ·
          refine ⟨773709940121327983272848345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515806626747551988848565563 773709940121327983272848345)
          ·
            refine ⟨580282455090995987454636259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 773709940121327983272848345 580282455090995987454636259)
            ·
              refine ⟨870423682636493981181954389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580282455090995987454636259 870423682636493981181954389)
              ·
                refine ⟨2550069382724103460494007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 870423682636493981181954389 2550069382724103460494007)
                ·
                  refine ⟨3825104074086155190741011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550069382724103460494007 3825104074086155190741011)
                  ·
                    refine ⟨5737656111129232786111517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3825104074086155190741011 5737656111129232786111517)
                    ·
                      refine ⟨2151621041673462294791819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5737656111129232786111517 2151621041673462294791819)
                      ·
                        rfl

theorem cell23_4190267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 1, 1, 3].length) (baseStart_4190267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190267 prefixEnd_4190267 := by exact prefixLift 4190267
  have htrace : WordTrace (prefixWord ++ tailWord_4190267) baseStart_4190267 baseEnd_4190267 := by
    simpa [prefixWord, tailWord_4190267, baseEnd_4190267] using wordTrace_append hprefix tailTrace_4190267
  have hstable : (prefixWord ++ tailWord_4190267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190267).length < 2 ^ (prefixWord ++ tailWord_4190267).sum := by decide
  have hdescent : baseEnd_4190267 < baseStart_4190267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190300 : List Nat := [2, 2, 4, 1, 1, 2, 2, 2, 1, 6]
def baseStart_4190300 : Nat := 118140960795 + 4190300 * 2 ^ 59
def prefixEnd_4190300 : Nat := 4983230072969 + 3 ^ 40 * 4190300 * 2
def baseEnd_4190300 : Nat := 717212662178353555226389

theorem tailTrace_4190300 : CollatzResearch.WordTrace tailWord_4190300 prefixEnd_4190300 717212662178353555226389 := by
  unfold tailWord_4190300
  simp only [CollatzResearch.WordTrace]
  refine ⟨76416398359633110554800177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101888531146177480739733569 76416398359633110554800177)
  ·
    refine ⟨57312298769724832916100133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76416398359633110554800177 57312298769724832916100133)
    ·
      refine ⟨10746056019323406171768775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57312298769724832916100133 10746056019323406171768775)
      ·
        refine ⟨16119084028985109257653163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10746056019323406171768775 16119084028985109257653163)
        ·
          refine ⟨24178626043477663886479745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16119084028985109257653163 24178626043477663886479745)
          ·
            refine ⟨18133969532608247914859809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24178626043477663886479745 18133969532608247914859809)
            ·
              refine ⟨13600477149456185936144857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18133969532608247914859809 13600477149456185936144857)
              ·
                refine ⟨10200357862092139452108643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13600477149456185936144857 10200357862092139452108643)
                ·
                  refine ⟨15300536793138209178162965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10200357862092139452108643 15300536793138209178162965)
                  ·
                    refine ⟨717212662178353555226389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15300536793138209178162965 717212662178353555226389)
                    ·
                      rfl

theorem cell23_4190300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_4190300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190300 prefixEnd_4190300 := by exact prefixLift 4190300
  have htrace : WordTrace (prefixWord ++ tailWord_4190300) baseStart_4190300 baseEnd_4190300 := by
    simpa [prefixWord, tailWord_4190300, baseEnd_4190300] using wordTrace_append hprefix tailTrace_4190300
  have hstable : (prefixWord ++ tailWord_4190300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190300).length < 2 ^ (prefixWord ++ tailWord_4190300).sum := by decide
  have hdescent : baseEnd_4190300 < baseStart_4190300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190301 : List Nat := [1, 4, 4, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_4190301 : Nat := 118140960795 + 4190301 * 2 ^ 59
def prefixEnd_4190301 : Nat := 4983230072969 + 3 ^ 40 * 4190301 * 2
def baseEnd_4190301 : Nat := 2151638500015715161766663

theorem tailTrace_4190301 : CollatzResearch.WordTrace tailWord_4190301 prefixEnd_4190301 2151638500015715161766663 := by
  unfold tailWord_4190301
  simp only [CollatzResearch.WordTrace]
  refine ⟨152832833192262598280386757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101888555461508398853591171 152832833192262598280386757)
  ·
    refine ⟨28656156223549237177572517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152832833192262598280386757 28656156223549237177572517)
    ·
      refine ⟨5373029291915481970794847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28656156223549237177572517 5373029291915481970794847)
      ·
        refine ⟨8059543937873222956192271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5373029291915481970794847 8059543937873222956192271)
        ·
          refine ⟨12089315906809834434288407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8059543937873222956192271 12089315906809834434288407)
          ·
            refine ⟨18133973860214751651432611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12089315906809834434288407 18133973860214751651432611)
            ·
              refine ⟨27200960790322127477148917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18133973860214751651432611 27200960790322127477148917)
              ·
                refine ⟨2550090074092699450982711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27200960790322127477148917 2550090074092699450982711)
                ·
                  refine ⟨3825135111139049176474067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550090074092699450982711 3825135111139049176474067)
                  ·
                    refine ⟨5737702666708573764711101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3825135111139049176474067 5737702666708573764711101)
                    ·
                      refine ⟨2151638500015715161766663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5737702666708573764711101 2151638500015715161766663)
                      ·
                        rfl

theorem cell23_4190301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_4190301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190301 prefixEnd_4190301 := by exact prefixLift 4190301
  have htrace : WordTrace (prefixWord ++ tailWord_4190301) baseStart_4190301 baseEnd_4190301 := by
    simpa [prefixWord, tailWord_4190301, baseEnd_4190301] using wordTrace_append hprefix tailTrace_4190301
  have hstable : (prefixWord ++ tailWord_4190301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190301).length < 2 ^ (prefixWord ++ tailWord_4190301).sum := by decide
  have hdescent : baseEnd_4190301 < baseStart_4190301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190303 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 4]
def baseStart_4190303 : Nat := 118140960795 + 4190303 * 2 ^ 59
def prefixEnd_4190303 : Nat := 4983230072969 + 3 ^ 40 * 4190303 * 2
def baseEnd_4190303 : Nat := 2151639526977024153941653

theorem tailTrace_4190303 : CollatzResearch.WordTrace tailWord_4190303 prefixEnd_4190303 2151639526977024153941653 := by
  unfold tailWord_4190303
  simp only [CollatzResearch.WordTrace]
  refine ⟨152832906138255352621959563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101888604092170235081306375 152832906138255352621959563)
  ·
    refine ⟨229249359207383028932939345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152832906138255352621959563 229249359207383028932939345)
    ·
      refine ⟨171937019405537271699704509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229249359207383028932939345 171937019405537271699704509)
      ·
        refine ⟨64476382277076476887389191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171937019405537271699704509 64476382277076476887389191)
        ·
          refine ⟨96714573415614715331083787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64476382277076476887389191 96714573415614715331083787)
          ·
            refine ⟨145071860123422072996625681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96714573415614715331083787 145071860123422072996625681)
            ·
              refine ⟨108803895092566554747469261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145071860123422072996625681 108803895092566554747469261)
              ·
                refine ⟨40801460659712458030300973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108803895092566554747469261 40801460659712458030300973)
                ·
                  refine ⟨15300547747392171761362865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40801460659712458030300973 15300547747392171761362865)
                  ·
                    refine ⟨11475410810544128821022149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15300547747392171761362865 11475410810544128821022149)
                    ·
                      refine ⟨2151639526977024153941653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11475410810544128821022149 2151639526977024153941653)
                      ·
                        rfl

theorem cell23_4190303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_4190303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190303 prefixEnd_4190303 := by exact prefixLift 4190303
  have htrace : WordTrace (prefixWord ++ tailWord_4190303) baseStart_4190303 baseEnd_4190303 := by
    simpa [prefixWord, tailWord_4190303, baseEnd_4190303] using wordTrace_append hprefix tailTrace_4190303
  have hstable : (prefixWord ++ tailWord_4190303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190303).length < 2 ^ (prefixWord ++ tailWord_4190303).sum := by decide
  have hdescent : baseEnd_4190303 < baseStart_4190303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190307 : List Nat := [1, 1, 1, 5, 1, 1, 6, 1, 1, 1, 4]
def baseStart_4190307 : Nat := 118140960795 + 4190307 * 2 ^ 59
def prefixEnd_4190307 : Nat := 4983230072969 + 3 ^ 40 * 4190307 * 2
def baseEnd_4190307 : Nat := 2151641580899642138291635

theorem tailTrace_4190307 : CollatzResearch.WordTrace tailWord_4190307 prefixEnd_4190307 2151641580899642138291635 := by
  unfold tailWord_4190307
  simp only [CollatzResearch.WordTrace]
  refine ⟨152833052030240861305105175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101888701353493907536736783 152833052030240861305105175)
  ·
    refine ⟨229249578045361291957657763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152833052030240861305105175 229249578045361291957657763)
    ·
      refine ⟨343874367068041937936486645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229249578045361291957657763 343874367068041937936486645)
      ·
        refine ⟨32238221912628931681545623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 343874367068041937936486645 32238221912628931681545623)
        ·
          refine ⟨48357332868943397522318435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32238221912628931681545623 48357332868943397522318435)
          ·
            refine ⟨72535999303415096283477653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48357332868943397522318435 72535999303415096283477653)
            ·
              refine ⟨3400124967347582638288015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72535999303415096283477653 3400124967347582638288015)
              ·
                refine ⟨5100187451021373957432023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3400124967347582638288015 5100187451021373957432023)
                ·
                  refine ⟨7650281176532060936148035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5100187451021373957432023 7650281176532060936148035)
                  ·
                    refine ⟨11475421764798091404222053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7650281176532060936148035 11475421764798091404222053)
                    ·
                      refine ⟨2151641580899642138291635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11475421764798091404222053 2151641580899642138291635)
                      ·
                        rfl

theorem cell23_4190307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_4190307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190307 prefixEnd_4190307 := by exact prefixLift 4190307
  have htrace : WordTrace (prefixWord ++ tailWord_4190307) baseStart_4190307 baseEnd_4190307 := by
    simpa [prefixWord, tailWord_4190307, baseEnd_4190307] using wordTrace_append hprefix tailTrace_4190307
  have hstable : (prefixWord ++ tailWord_4190307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190307).length < 2 ^ (prefixWord ++ tailWord_4190307).sum := by decide
  have hdescent : baseEnd_4190307 < baseStart_4190307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190323 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 3]
def baseStart_4190323 : Nat := 118140960795 + 4190323 * 2 ^ 59
def prefixEnd_4190323 : Nat := 4983230072969 + 3 ^ 40 * 4190323 * 2
def baseEnd_4190323 : Nat := 2151649796590114075691561

theorem tailTrace_4190323 : CollatzResearch.WordTrace tailWord_4190323 prefixEnd_4190323 2151649796590114075691561 := by
  unfold tailWord_4190323
  simp only [CollatzResearch.WordTrace]
  refine ⟨152833635598182896037687623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101889090398788597358458415 152833635598182896037687623)
  ·
    refine ⟨229250453397274344056531435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152833635598182896037687623 229250453397274344056531435)
    ·
      refine ⟨343875680095911516084797153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229250453397274344056531435 343875680095911516084797153)
      ·
        refine ⟨257906760071933637063597865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343875680095911516084797153 257906760071933637063597865)
        ·
          refine ⟨193430070053950227797698399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257906760071933637063597865 193430070053950227797698399)
          ·
            refine ⟨290145105080925341696547599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193430070053950227797698399 290145105080925341696547599)
            ·
              refine ⟨435217657621388012544821399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290145105080925341696547599 435217657621388012544821399)
              ·
                refine ⟨652826486432082018817232099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435217657621388012544821399 652826486432082018817232099)
                ·
                  refine ⟨979239729648123028225848149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652826486432082018817232099 979239729648123028225848149)
                  ·
                    refine ⟨5737732790906970868510829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 979239729648123028225848149 5737732790906970868510829)
                    ·
                      refine ⟨2151649796590114075691561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5737732790906970868510829 2151649796590114075691561)
                      ·
                        rfl

theorem cell23_4190323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 3].length) (baseStart_4190323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190323 prefixEnd_4190323 := by exact prefixLift 4190323
  have htrace : WordTrace (prefixWord ++ tailWord_4190323) baseStart_4190323 baseEnd_4190323 := by
    simpa [prefixWord, tailWord_4190323, baseEnd_4190323] using wordTrace_append hprefix tailTrace_4190323
  have hstable : (prefixWord ++ tailWord_4190323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190323).length < 2 ^ (prefixWord ++ tailWord_4190323).sum := by decide
  have hdescent : baseEnd_4190323 < baseStart_4190323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190343 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 2, 7]
def baseStart_4190343 : Nat := 118140960795 + 4190343 * 2 ^ 59
def prefixEnd_4190343 : Nat := 4983230072969 + 3 ^ 40 * 4190343 * 2
def baseEnd_4190343 : Nat := 717220022067734665813823

theorem tailTrace_4190343 : CollatzResearch.WordTrace tailWord_4190343 prefixEnd_4190343 717220022067734665813823 := by
  unfold tailWord_4190343
  simp only [CollatzResearch.WordTrace]
  refine ⟨152834365058110439453415683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101889576705406959635610455 152834365058110439453415683)
  ·
    refine ⟨229251547587165659180123525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152834365058110439453415683 229251547587165659180123525)
    ·
      refine ⟨42984665172593561096273161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229251547587165659180123525 42984665172593561096273161)
      ·
        refine ⟨32238498879445170822204871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42984665172593561096273161 32238498879445170822204871)
        ·
          refine ⟨48357748319167756233307307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32238498879445170822204871 48357748319167756233307307)
          ·
            refine ⟨72536622478751634349960961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48357748319167756233307307 72536622478751634349960961)
            ·
              refine ⟨54402466859063725762470721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72536622478751634349960961 54402466859063725762470721)
              ·
                refine ⟨40801850144297794321853041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54402466859063725762470721 40801850144297794321853041)
                ·
                  refine ⟨30601387608223345741389781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40801850144297794321853041 30601387608223345741389781)
                  ·
                    refine ⟨717220022067734665813823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30601387608223345741389781 717220022067734665813823)
                    ·
                      rfl

theorem cell23_4190343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_4190343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190343 prefixEnd_4190343 := by exact prefixLift 4190343
  have htrace : WordTrace (prefixWord ++ tailWord_4190343) baseStart_4190343 baseEnd_4190343 := by
    simpa [prefixWord, tailWord_4190343, baseEnd_4190343] using wordTrace_append hprefix tailTrace_4190343
  have hstable : (prefixWord ++ tailWord_4190343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190343).length < 2 ^ (prefixWord ++ tailWord_4190343).sum := by decide
  have hdescent : baseEnd_4190343 < baseStart_4190343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190344 : List Nat := [2, 1, 3, 4, 1, 2, 2, 2, 1, 2, 3]
def baseStart_4190344 : Nat := 118140960795 + 4190344 * 2 ^ 59
def prefixEnd_4190344 : Nat := 4983230072969 + 3 ^ 40 * 4190344 * 2
def baseEnd_4190344 : Nat := 2151660579683858493528965

theorem tailTrace_4190344 : CollatzResearch.WordTrace tailWord_4190344 prefixEnd_4190344 2151660579683858493528965 := by
  unfold tailWord_4190344
  simp only [CollatzResearch.WordTrace]
  refine ⟨76417200765553408312101043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101889601020737877749468057 76417200765553408312101043)
  ·
    refine ⟨114625801148330112468151565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76417200765553408312101043 114625801148330112468151565)
    ·
      refine ⟨42984675430623792175556837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114625801148330112468151565 42984675430623792175556837)
      ·
        refine ⟨8059626643241961032916907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42984675430623792175556837 8059626643241961032916907)
        ·
          refine ⟨12089439964862941549375361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8059626643241961032916907 12089439964862941549375361)
          ·
            refine ⟨9067079973647206162031521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12089439964862941549375361 9067079973647206162031521)
            ·
              refine ⟨6800309980235404621523641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9067079973647206162031521 6800309980235404621523641)
              ·
                refine ⟨5100232485176553466142731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6800309980235404621523641 5100232485176553466142731)
                ·
                  refine ⟨7650348727764830199214097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5100232485176553466142731 7650348727764830199214097)
                  ·
                    refine ⟨5737761545823622649410573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7650348727764830199214097 5737761545823622649410573)
                    ·
                      refine ⟨2151660579683858493528965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5737761545823622649410573 2151660579683858493528965)
                      ·
                        rfl

theorem cell23_4190344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_4190344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190344 prefixEnd_4190344 := by exact prefixLift 4190344
  have htrace : WordTrace (prefixWord ++ tailWord_4190344) baseStart_4190344 baseEnd_4190344 := by
    simpa [prefixWord, tailWord_4190344, baseEnd_4190344] using wordTrace_append hprefix tailTrace_4190344
  have hstable : (prefixWord ++ tailWord_4190344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190344).length < 2 ^ (prefixWord ++ tailWord_4190344).sum := by decide
  have hdescent : baseEnd_4190344 < baseStart_4190344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190363 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 4]
def baseStart_4190363 : Nat := 118140960795 + 4190363 * 2 ^ 59
def prefixEnd_4190363 : Nat := 4983230072969 + 3 ^ 40 * 4190363 * 2
def baseEnd_4190363 : Nat := 2151670335816293919191377

theorem tailTrace_4190363 : CollatzResearch.WordTrace tailWord_4190363 prefixEnd_4190363 2151670335816293919191377 := by
  unfold tailWord_4190363
  simp only [CollatzResearch.WordTrace]
  refine ⟨152835094518037982869143743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101890063012025321912762495 152835094518037982869143743)
  ·
    refine ⟨229252641777056974303715615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152835094518037982869143743 229252641777056974303715615)
    ·
      refine ⟨343878962665585461455573423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229252641777056974303715615 343878962665585461455573423)
      ·
        refine ⟨515818443998378192183360135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343878962665585461455573423 515818443998378192183360135)
        ·
          refine ⟨773727665997567288275040203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515818443998378192183360135 773727665997567288275040203)
          ·
            refine ⟨1160591498996350932412560305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773727665997567288275040203 1160591498996350932412560305)
            ·
              refine ⟨870443624247263199309420229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1160591498996350932412560305 870443624247263199309420229)
              ·
                refine ⟨163208179546361849870516293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 870443624247263199309420229 163208179546361849870516293)
                ·
                  refine ⟨30601533664942846850721805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163208179546361849870516293 30601533664942846850721805)
                  ·
                    refine ⟨11475575124353567569020677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30601533664942846850721805 11475575124353567569020677)
                    ·
                      refine ⟨2151670335816293919191377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11475575124353567569020677 2151670335816293919191377)
                      ·
                        rfl

theorem cell23_4190363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 4].length) (baseStart_4190363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190363 prefixEnd_4190363 := by exact prefixLift 4190363
  have htrace : WordTrace (prefixWord ++ tailWord_4190363) baseStart_4190363 baseEnd_4190363 := by
    simpa [prefixWord, tailWord_4190363, baseEnd_4190363] using wordTrace_append hprefix tailTrace_4190363
  have hstable : (prefixWord ++ tailWord_4190363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190363).length < 2 ^ (prefixWord ++ tailWord_4190363).sum := by decide
  have hdescent : baseEnd_4190363 < baseStart_4190363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190375 : List Nat := [1, 1, 6, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_4190375 : Nat := 118140960795 + 4190375 * 2 ^ 59
def prefixEnd_4190375 : Nat := 4983230072969 + 3 ^ 40 * 4190375 * 2
def baseEnd_4190375 : Nat := 2151676497584147872241323

theorem tailTrace_4190375 : CollatzResearch.WordTrace tailWord_4190375 prefixEnd_4190375 2151676497584147872241323 := by
  unfold tailWord_4190375
  simp only [CollatzResearch.WordTrace]
  refine ⟨152835532193994508918580579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101890354795996339279053719 152835532193994508918580579)
  ·
    refine ⟨229253298290991763377870869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152835532193994508918580579 229253298290991763377870869)
    ·
      refine ⟨10746248357390238908337697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 229253298290991763377870869 10746248357390238908337697)
      ·
        refine ⟨8059686268042679181253273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10746248357390238908337697 8059686268042679181253273)
        ·
          refine ⟨6044764701032009385939955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8059686268042679181253273 6044764701032009385939955)
          ·
            refine ⟨9067147051548014078909933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6044764701032009385939955 9067147051548014078909933)
            ·
              refine ⟨3400180144330505279591225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9067147051548014078909933 3400180144330505279591225)
              ·
                refine ⟨2550135108247878959693419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3400180144330505279591225 2550135108247878959693419)
                ·
                  refine ⟨3825202662371818439540129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550135108247878959693419 3825202662371818439540129)
                  ·
                    refine ⟨2868901996778863829655097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3825202662371818439540129 2868901996778863829655097)
                    ·
                      refine ⟨2151676497584147872241323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2868901996778863829655097 2151676497584147872241323)
                      ·
                        rfl

theorem cell23_4190375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_4190375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190375 prefixEnd_4190375 := by exact prefixLift 4190375
  have htrace : WordTrace (prefixWord ++ tailWord_4190375) baseStart_4190375 baseEnd_4190375 := by
    simpa [prefixWord, tailWord_4190375, baseEnd_4190375] using wordTrace_append hprefix tailTrace_4190375
  have hstable : (prefixWord ++ tailWord_4190375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190375).length < 2 ^ (prefixWord ++ tailWord_4190375).sum := by decide
  have hdescent : baseEnd_4190375 < baseStart_4190375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190383 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 5]
def baseStart_4190383 : Nat := 118140960795 + 4190383 * 2 ^ 59
def prefixEnd_4190383 : Nat := 4983230072969 + 3 ^ 40 * 4190383 * 2
def baseEnd_4190383 : Nat := 2151680605429383840941285

theorem tailTrace_4190383 : CollatzResearch.WordTrace tailWord_4190383 prefixEnd_4190383 2151680605429383840941285 := by
  unfold tailWord_4190383
  simp only [CollatzResearch.WordTrace]
  refine ⟨152835823977965526284871803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101890549318643684189914535 152835823977965526284871803)
  ·
    refine ⟨229253735966948289427307705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152835823977965526284871803 229253735966948289427307705)
    ·
      refine ⟨171940301975211217070480779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229253735966948289427307705 171940301975211217070480779)
      ·
        refine ⟨257910452962816825605721169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171940301975211217070480779 257910452962816825605721169)
        ·
          refine ⟨193432839722112619204290877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257910452962816825605721169 193432839722112619204290877)
          ·
            refine ⟨72537314895792232201609079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193432839722112619204290877 72537314895792232201609079)
            ·
              refine ⟨108805972343688348302413619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72537314895792232201609079 108805972343688348302413619)
              ·
                refine ⟨163208958515532522453620429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108805972343688348302413619 163208958515532522453620429)
                ·
                  refine ⟨61203359443324695920107661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163208958515532522453620429 61203359443324695920107661)
                  ·
                    refine ⟨22951259791246760970040373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61203359443324695920107661 22951259791246760970040373)
                    ·
                      refine ⟨2151680605429383840941285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22951259791246760970040373 2151680605429383840941285)
                      ·
                        rfl

theorem cell23_4190383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_4190383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190383 prefixEnd_4190383 := by exact prefixLift 4190383
  have htrace : WordTrace (prefixWord ++ tailWord_4190383) baseStart_4190383 baseEnd_4190383 := by
    simpa [prefixWord, tailWord_4190383, baseEnd_4190383] using wordTrace_append hprefix tailTrace_4190383
  have hstable : (prefixWord ++ tailWord_4190383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190383).length < 2 ^ (prefixWord ++ tailWord_4190383).sum := by decide
  have hdescent : baseEnd_4190383 < baseStart_4190383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190391 : List Nat := [1, 1, 3, 1, 4, 4, 2, 1, 2, 1, 3]
def baseStart_4190391 : Nat := 118140960795 + 4190391 * 2 ^ 59
def prefixEnd_4190391 : Nat := 4983230072969 + 3 ^ 40 * 4190391 * 2
def baseEnd_4190391 : Nat := 2151684713274619809641249

theorem tailTrace_4190391 : CollatzResearch.WordTrace tailWord_4190391 prefixEnd_4190391 2151684713274619809641249 := by
  unfold tailWord_4190391
  simp only [CollatzResearch.WordTrace]
  refine ⟨152836115761936543651163027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101890743841291029100775351 152836115761936543651163027)
  ·
    refine ⟨229254173642904815476744541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152836115761936543651163027 229254173642904815476744541)
    ·
      refine ⟨85970315116089305803779203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229254173642904815476744541 85970315116089305803779203)
      ·
        refine ⟨128955472674133958705668805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85970315116089305803779203 128955472674133958705668805)
        ·
          refine ⟨24179151126400117257312901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128955472674133958705668805 24179151126400117257312901)
          ·
            refine ⟨4533590836200021985746169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24179151126400117257312901 4533590836200021985746169)
            ·
              refine ⟨3400193127150016489309627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4533590836200021985746169 3400193127150016489309627)
              ·
                refine ⟨5100289690725024733964441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3400193127150016489309627 5100289690725024733964441)
                ·
                  refine ⟨3825217268043768550473331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5100289690725024733964441 3825217268043768550473331)
                  ·
                    refine ⟨5737825902065652825709997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3825217268043768550473331 5737825902065652825709997)
                    ·
                      refine ⟨2151684713274619809641249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5737825902065652825709997 2151684713274619809641249)
                      ·
                        rfl

theorem cell23_4190391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 2, 1, 3].length) (baseStart_4190391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190391 prefixEnd_4190391 := by exact prefixLift 4190391
  have htrace : WordTrace (prefixWord ++ tailWord_4190391) baseStart_4190391 baseEnd_4190391 := by
    simpa [prefixWord, tailWord_4190391, baseEnd_4190391] using wordTrace_append hprefix tailTrace_4190391
  have hstable : (prefixWord ++ tailWord_4190391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190391).length < 2 ^ (prefixWord ++ tailWord_4190391).sum := by decide
  have hdescent : baseEnd_4190391 < baseStart_4190391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190397 : List Nat := [1, 4, 1, 2, 1, 1, 1, 5, 1, 4, 2]
def baseStart_4190397 : Nat := 118140960795 + 4190397 * 2 ^ 59
def prefixEnd_4190397 : Nat := 4983230072969 + 3 ^ 40 * 4190397 * 2
def baseEnd_4190397 : Nat := 2151687794158546786166221

theorem tailTrace_4190397 : CollatzResearch.WordTrace tailWord_4190397 prefixEnd_4190397 2151687794158546786166221 := by
  unfold tailWord_4190397
  simp only [CollatzResearch.WordTrace]
  refine ⟨152836334599914806675881445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101890889733276537783920963 152836334599914806675881445)
  ·
    refine ⟨28656812737484026251727771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152836334599914806675881445 28656812737484026251727771)
    ·
      refine ⟨42985219106226039377591657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28656812737484026251727771 42985219106226039377591657)
      ·
        refine ⟨32238914329669529533193743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42985219106226039377591657 32238914329669529533193743)
        ·
          refine ⟨48358371494504294299790615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32238914329669529533193743 48358371494504294299790615)
          ·
            refine ⟨72537557241756441449685923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48358371494504294299790615 72537557241756441449685923)
            ·
              refine ⟨108806335862634662174528885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72537557241756441449685923 108806335862634662174528885)
              ·
                refine ⟨10200593987121999578862083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108806335862634662174528885 10200593987121999578862083)
                ·
                  refine ⟨15300890980682999368293125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10200593987121999578862083 15300890980682999368293125)
                  ·
                    refine ⟨2868917058878062381554961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15300890980682999368293125 2868917058878062381554961)
                    ·
                      refine ⟨2151687794158546786166221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2868917058878062381554961 2151687794158546786166221)
                      ·
                        rfl

theorem cell23_4190397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_4190397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190397 prefixEnd_4190397 := by exact prefixLift 4190397
  have htrace : WordTrace (prefixWord ++ tailWord_4190397) baseStart_4190397 baseEnd_4190397 := by
    simpa [prefixWord, tailWord_4190397, baseEnd_4190397] using wordTrace_append hprefix tailTrace_4190397
  have hstable : (prefixWord ++ tailWord_4190397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190397).length < 2 ^ (prefixWord ++ tailWord_4190397).sum := by decide
  have hdescent : baseEnd_4190397 < baseStart_4190397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190400 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 5]
def baseStart_4190400 : Nat := 118140960795 + 4190400 * 2 ^ 59
def prefixEnd_4190400 : Nat := 4983230072969 + 3 ^ 40 * 4190400 * 2
def baseEnd_4190400 : Nat := 2151689334600510274428707

theorem tailTrace_4190400 : CollatzResearch.WordTrace tailWord_4190400 prefixEnd_4190400 2151689334600510274428707 := by
  unfold tailWord_4190400
  simp only [CollatzResearch.WordTrace]
  refine ⟨76418222009451969094120327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101890962679269292125493769 76418222009451969094120327)
  ·
    refine ⟨114627333014177953641180491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76418222009451969094120327 114627333014177953641180491)
    ·
      refine ⟨171940999521266930461770737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114627333014177953641180491 171940999521266930461770737)
      ·
        refine ⟨128955749640950197846328053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171940999521266930461770737 128955749640950197846328053)
        ·
          refine ⟨12089601528839081048093255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128955749640950197846328053 12089601528839081048093255)
          ·
            refine ⟨18134402293258621572139883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12089601528839081048093255 18134402293258621572139883)
            ·
              refine ⟨27201603439887932358209825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18134402293258621572139883 27201603439887932358209825)
              ·
                refine ⟨20401202579915949268657369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27201603439887932358209825 20401202579915949268657369)
                ·
                  refine ⟨15300901934936961951493027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20401202579915949268657369 15300901934936961951493027)
                  ·
                    refine ⟨22951352902405442927239541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15300901934936961951493027 22951352902405442927239541)
                    ·
                      refine ⟨2151689334600510274428707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22951352902405442927239541 2151689334600510274428707)
                      ·
                        rfl

theorem cell23_4190400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_4190400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190400 prefixEnd_4190400 := by exact prefixLift 4190400
  have htrace : WordTrace (prefixWord ++ tailWord_4190400) baseStart_4190400 baseEnd_4190400 := by
    simpa [prefixWord, tailWord_4190400, baseEnd_4190400] using wordTrace_append hprefix tailTrace_4190400
  have hstable : (prefixWord ++ tailWord_4190400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190400).length < 2 ^ (prefixWord ++ tailWord_4190400).sum := by decide
  have hdescent : baseEnd_4190400 < baseStart_4190400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190401 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_4190401 : Nat := 118140960795 + 4190401 * 2 ^ 59
def prefixEnd_4190401 : Nat := 4983230072969 + 3 ^ 40 * 4190401 * 2
def baseEnd_4190401 : Nat := 2151689848081164770516203

theorem tailTrace_4190401 : CollatzResearch.WordTrace tailWord_4190401 prefixEnd_4190401 2151689848081164770516203 := by
  unfold tailWord_4190401
  simp only [CollatzResearch.WordTrace]
  refine ⟨152836480491900315359027057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101890986994600210239351371 152836480491900315359027057)
  ·
    refine ⟨114627360368925236519270293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152836480491900315359027057 114627360368925236519270293)
    ·
      refine ⟨5373157517293370461840795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 114627360368925236519270293 5373157517293370461840795)
      ·
        refine ⟨8059736275940055692761193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5373157517293370461840795 8059736275940055692761193)
        ·
          refine ⟨6044802206955041769570895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8059736275940055692761193 6044802206955041769570895)
          ·
            refine ⟨9067203310432562654356343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6044802206955041769570895 9067203310432562654356343)
            ·
              refine ⟨13600804965648843981534515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9067203310432562654356343 13600804965648843981534515)
              ·
                refine ⟨20401207448473265972301773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13600804965648843981534515 20401207448473265972301773)
                ·
                  refine ⟨7650452793177474739613165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20401207448473265972301773 7650452793177474739613165)
                  ·
                    refine ⟨2868919797441553027354937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7650452793177474739613165 2868919797441553027354937)
                    ·
                      refine ⟨2151689848081164770516203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2868919797441553027354937 2151689848081164770516203)
                      ·
                        rfl

theorem cell23_4190401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_4190401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190401 prefixEnd_4190401 := by exact prefixLift 4190401
  have htrace : WordTrace (prefixWord ++ tailWord_4190401) baseStart_4190401 baseEnd_4190401 := by
    simpa [prefixWord, tailWord_4190401, baseEnd_4190401] using wordTrace_append hprefix tailTrace_4190401
  have hstable : (prefixWord ++ tailWord_4190401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190401).length < 2 ^ (prefixWord ++ tailWord_4190401).sum := by decide
  have hdescent : baseEnd_4190401 < baseStart_4190401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190414 : List Nat := [4, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2]
def baseStart_4190414 : Nat := 118140960795 + 4190414 * 2 ^ 59
def prefixEnd_4190414 : Nat := 4983230072969 + 3 ^ 40 * 4190414 * 2
def baseEnd_4190414 : Nat := 2151696523329673219653643

theorem tailTrace_4190414 : CollatzResearch.WordTrace tailWord_4190414 prefixEnd_4190414 2151696523329673219653643 := by
  unfold tailWord_4190414
  simp only [CollatzResearch.WordTrace]
  refine ⟨19104619330106652322406287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101891303093902145719500197 19104619330106652322406287)
  ·
    refine ⟨28656928995159978483609431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19104619330106652322406287 28656928995159978483609431)
    ·
      refine ⟨42985393492739967725414147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28656928995159978483609431 42985393492739967725414147)
      ·
        refine ⟨64478090239109951588121221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42985393492739967725414147 64478090239109951588121221)
        ·
          refine ⟨12089641919833115922772729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64478090239109951588121221 12089641919833115922772729)
          ·
            refine ⟨9067231439874836942079547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12089641919833115922772729 9067231439874836942079547)
            ·
              refine ⟨13600847159812255413119321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9067231439874836942079547 13600847159812255413119321)
              ·
                refine ⟨10200635369859191559839491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13600847159812255413119321 10200635369859191559839491)
                ·
                  refine ⟨15300953054788787339759237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10200635369859191559839491 15300953054788787339759237)
                  ·
                    refine ⟨2868928697772897626204857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15300953054788787339759237 2868928697772897626204857)
                    ·
                      refine ⟨2151696523329673219653643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2868928697772897626204857 2151696523329673219653643)
                      ·
                        rfl

theorem cell23_4190414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_4190414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190414 prefixEnd_4190414 := by exact prefixLift 4190414
  have htrace : WordTrace (prefixWord ++ tailWord_4190414) baseStart_4190414 baseEnd_4190414 := by
    simpa [prefixWord, tailWord_4190414, baseEnd_4190414] using wordTrace_append hprefix tailTrace_4190414
  have hstable : (prefixWord ++ tailWord_4190414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190414).length < 2 ^ (prefixWord ++ tailWord_4190414).sum := by decide
  have hdescent : baseEnd_4190414 < baseStart_4190414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190447 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 3]
def baseStart_4190447 : Nat := 118140960795 + 4190447 * 2 ^ 59
def prefixEnd_4190447 : Nat := 4983230072969 + 3 ^ 40 * 4190447 * 2
def baseEnd_4190447 : Nat := 2151713468191271590540991

theorem tailTrace_4190447 : CollatzResearch.WordTrace tailWord_4190447 prefixEnd_4190447 2151713468191271590540991 := by
  unfold tailWord_4190447
  simp only [CollatzResearch.WordTrace]
  refine ⟨152838158249733665215201595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101892105499822443476801063 152838158249733665215201595)
  ·
    refine ⟨229257237374600497822802393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152838158249733665215201595 229257237374600497822802393)
    ·
      refine ⟨171942928030950373367101795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229257237374600497822802393 171942928030950373367101795)
      ·
        refine ⟨257914392046425560050652693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171942928030950373367101795 257914392046425560050652693)
        ·
          refine ⟨12089737127176198127374345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 257914392046425560050652693 12089737127176198127374345)
          ·
            refine ⟨9067302845382148595530759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12089737127176198127374345 9067302845382148595530759)
            ·
              refine ⟨13600954268073222893296139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9067302845382148595530759 13600954268073222893296139)
              ·
                refine ⟨20401431402109834339944209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13600954268073222893296139 20401431402109834339944209)
                ·
                  refine ⟨15301073551582375754958157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20401431402109834339944209 15301073551582375754958157)
                  ·
                    refine ⟨5737902581843390908109309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15301073551582375754958157 5737902581843390908109309)
                    ·
                      refine ⟨2151713468191271590540991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5737902581843390908109309 2151713468191271590540991)
                      ·
                        rfl

theorem cell23_4190447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 3].length) (baseStart_4190447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190447 prefixEnd_4190447 := by exact prefixLift 4190447
  have htrace : WordTrace (prefixWord ++ tailWord_4190447) baseStart_4190447 baseEnd_4190447 := by
    simpa [prefixWord, tailWord_4190447, baseEnd_4190447] using wordTrace_append hprefix tailTrace_4190447
  have hstable : (prefixWord ++ tailWord_4190447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190447).length < 2 ^ (prefixWord ++ tailWord_4190447).sum := by decide
  have hdescent : baseEnd_4190447 < baseStart_4190447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190471 : List Nat := [1, 1, 4, 5, 1, 1, 2, 3, 5]
def baseStart_4190471 : Nat := 118140960795 + 4190471 * 2 ^ 59
def prefixEnd_4190471 : Nat := 4983230072969 + 3 ^ 40 * 4190471 * 2
def baseEnd_4190471 : Nat := 239080643525219944071209

theorem tailTrace_4190471 : CollatzResearch.WordTrace tailWord_4190471 prefixEnd_4190471 239080643525219944071209 := by
  unfold tailWord_4190471
  simp only [CollatzResearch.WordTrace]
  refine ⟨152839033601646717314075267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101892689067764478209383511 152839033601646717314075267)
  ·
    refine ⟨229258550402470075971112901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152839033601646717314075267 229258550402470075971112901)
    ·
      refine ⟨42985978200463139244583669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229258550402470075971112901 42985978200463139244583669)
      ·
        refine ⟨4029935456293419304179719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42985978200463139244583669 4029935456293419304179719)
        ·
          refine ⟨6044903184440128956269579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4029935456293419304179719 6044903184440128956269579)
          ·
            refine ⟨9067354776660193434404369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6044903184440128956269579 9067354776660193434404369)
            ·
              refine ⟨6800516082495145075803277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9067354776660193434404369 6800516082495145075803277)
              ·
                refine ⟨2550193530935679403426229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6800516082495145075803277 2550193530935679403426229)
                ·
                  refine ⟨239080643525219944071209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2550193530935679403426229 239080643525219944071209)
                  ·
                    rfl

theorem cell23_4190471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 5].length) (baseStart_4190471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190471 prefixEnd_4190471 := by exact prefixLift 4190471
  have htrace : WordTrace (prefixWord ++ tailWord_4190471) baseStart_4190471 baseEnd_4190471 := by
    simpa [prefixWord, tailWord_4190471, baseEnd_4190471] using wordTrace_append hprefix tailTrace_4190471
  have hstable : (prefixWord ++ tailWord_4190471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190471).length < 2 ^ (prefixWord ++ tailWord_4190471).sum := by decide
  have hdescent : baseEnd_4190471 < baseStart_4190471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190497 : List Nat := [1, 2, 3, 2, 1, 1, 3, 3, 3, 4]
def baseStart_4190497 : Nat := 118140960795 + 4190497 * 2 ^ 59
def prefixEnd_4190497 : Nat := 4983230072969 + 3 ^ 40 * 4190497 * 2
def baseEnd_4190497 : Nat := 717246380741332131638587

theorem tailTrace_4190497 : CollatzResearch.WordTrace tailWord_4190497 prefixEnd_4190497 717246380741332131638587 := by
  unfold tailWord_4190497
  simp only [CollatzResearch.WordTrace]
  refine ⟨152839981899552523754521745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101893321266368349169681163 152839981899552523754521745)
  ·
    refine ⟨114629986424664392815891309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152839981899552523754521745 114629986424664392815891309)
    ·
      refine ⟨42986244909249147305959241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114629986424664392815891309 42986244909249147305959241)
      ·
        refine ⟨32239683681936860479469431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42986244909249147305959241 32239683681936860479469431)
        ·
          refine ⟨48359525522905290719204147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32239683681936860479469431 48359525522905290719204147)
          ·
            refine ⟨72539288284357936078806221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48359525522905290719204147 72539288284357936078806221)
            ·
              refine ⟨27202233106634226029552333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72539288284357936078806221 27202233106634226029552333)
              ·
                refine ⟨10200837414987834761082125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27202233106634226029552333 10200837414987834761082125)
                ·
                  refine ⟨3825314030620438035405797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10200837414987834761082125 3825314030620438035405797)
                  ·
                    refine ⟨717246380741332131638587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3825314030620438035405797 717246380741332131638587)
                    ·
                      rfl

theorem cell23_4190497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_4190497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190497 prefixEnd_4190497 := by exact prefixLift 4190497
  have htrace : WordTrace (prefixWord ++ tailWord_4190497) baseStart_4190497 baseEnd_4190497 := by
    simpa [prefixWord, tailWord_4190497, baseEnd_4190497] using wordTrace_append hprefix tailTrace_4190497
  have hstable : (prefixWord ++ tailWord_4190497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190497).length < 2 ^ (prefixWord ++ tailWord_4190497).sum := by decide
  have hdescent : baseEnd_4190497 < baseStart_4190497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190547 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 3, 5, 2]
def baseStart_4190547 : Nat := 118140960795 + 4190547 * 2 ^ 59
def prefixEnd_4190547 : Nat := 4983230072969 + 3 ^ 40 * 4190547 * 2
def baseEnd_4190547 : Nat := 2151764816256721199290531

theorem tailTrace_4190547 : CollatzResearch.WordTrace tailWord_4190547 prefixEnd_4190547 2151764816256721199290531 := by
  unfold tailWord_4190547
  simp only [CollatzResearch.WordTrace]
  refine ⟨152841805549371382293841895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101894537032914254862561263 152841805549371382293841895)
  ·
    refine ⟨229262708324057073440762843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152841805549371382293841895 229262708324057073440762843)
    ·
      refine ⟨343894062486085610161144265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229262708324057073440762843 343894062486085610161144265)
      ·
        refine ⟨257920546864564207620858199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343894062486085610161144265 257920546864564207620858199)
        ·
          refine ⟨386880820296846311431287299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257920546864564207620858199 386880820296846311431287299)
          ·
            refine ⟨580321230445269467146930949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386880820296846311431287299 580321230445269467146930949)
            ·
              refine ⟨108810230708488025090049553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 580321230445269467146930949 108810230708488025090049553)
              ·
                refine ⟨81607673031366018817537165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108810230708488025090049553 81607673031366018817537165)
                ·
                  refine ⟨30602877386762257056576437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81607673031366018817537165 30602877386762257056576437)
                  ·
                    refine ⟨2869019755008961599054041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30602877386762257056576437 2869019755008961599054041)
                    ·
                      refine ⟨2151764816256721199290531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2869019755008961599054041 2151764816256721199290531)
                      ·
                        rfl

theorem cell23_4190547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 5, 2].length) (baseStart_4190547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190547 prefixEnd_4190547 := by exact prefixLift 4190547
  have htrace : WordTrace (prefixWord ++ tailWord_4190547) baseStart_4190547 baseEnd_4190547 := by
    simpa [prefixWord, tailWord_4190547, baseEnd_4190547] using wordTrace_append hprefix tailTrace_4190547
  have hstable : (prefixWord ++ tailWord_4190547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190547).length < 2 ^ (prefixWord ++ tailWord_4190547).sum := by decide
  have hdescent : baseEnd_4190547 < baseStart_4190547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190548 : List Nat := [2, 4, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_4190548 : Nat := 118140960795 + 4190548 * 2 ^ 59
def prefixEnd_4190548 : Nat := 4983230072969 + 3 ^ 40 * 4190548 * 2
def baseEnd_4190548 : Nat := 717255109912458565126009

theorem tailTrace_4190548 : CollatzResearch.WordTrace tailWord_4190548 prefixEnd_4190548 717255109912458565126009 := by
  unfold tailWord_4190548
  simp only [CollatzResearch.WordTrace]
  refine ⟨76420921011183879732314149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101894561348245172976418865 76420921011183879732314149)
  ·
    refine ⟨14328922689596977449808903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76420921011183879732314149 14328922689596977449808903)
    ·
      refine ⟨21493384034395466174713355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14328922689596977449808903 21493384034395466174713355)
      ·
        refine ⟨32240076051593199262070033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21493384034395466174713355 32240076051593199262070033)
        ·
          refine ⟨24180057038694899446552525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32240076051593199262070033 24180057038694899446552525)
          ·
            refine ⟨9067521389510587292457197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24180057038694899446552525 9067521389510587292457197)
            ·
              refine ⟨3400320521066470234671449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9067521389510587292457197 3400320521066470234671449)
              ·
                refine ⟨2550240390799852676003587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3400320521066470234671449 2550240390799852676003587)
                ·
                  refine ⟨3825360586199779014005381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550240390799852676003587 3825360586199779014005381)
                  ·
                    refine ⟨717255109912458565126009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3825360586199779014005381 717255109912458565126009)
                    ·
                      rfl

theorem cell23_4190548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_4190548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190548 prefixEnd_4190548 := by exact prefixLift 4190548
  have htrace : WordTrace (prefixWord ++ tailWord_4190548) baseStart_4190548 baseEnd_4190548 := by
    simpa [prefixWord, tailWord_4190548, baseEnd_4190548] using wordTrace_append hprefix tailTrace_4190548
  have hstable : (prefixWord ++ tailWord_4190548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190548).length < 2 ^ (prefixWord ++ tailWord_4190548).sum := by decide
  have hdescent : baseEnd_4190548 < baseStart_4190548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190564 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 4, 3, 2]
def baseStart_4190564 : Nat := 118140960795 + 4190564 * 2 ^ 59
def prefixEnd_4190564 : Nat := 4983230072969 + 3 ^ 40 * 4190564 * 2
def baseEnd_4190564 : Nat := 2151773545427847632777953

theorem tailTrace_4190564 : CollatzResearch.WordTrace tailWord_4190564 prefixEnd_4190564 2151773545427847632777953 := by
  unfold tailWord_4190564
  simp only [CollatzResearch.WordTrace]
  refine ⟨76421212795154897098605373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101894950393539862798140497 76421212795154897098605373)
  ·
    refine ⟨28657954798183086411977015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76421212795154897098605373 28657954798183086411977015)
    ·
      refine ⟨42986932197274629617965523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28657954798183086411977015 42986932197274629617965523)
      ·
        refine ⟨64480398295911944426948285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42986932197274629617965523 64480398295911944426948285)
        ·
          refine ⟨24180149360966979160105607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64480398295911944426948285 24180149360966979160105607)
          ·
            refine ⟨36270224041450468740158411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24180149360966979160105607 36270224041450468740158411)
            ·
              refine ⟨54405336062175703110237617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36270224041450468740158411 54405336062175703110237617)
              ·
                refine ⟨40804002046631777332678213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54405336062175703110237617 40804002046631777332678213)
                ·
                  refine ⟨7650750383743458249877165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40804002046631777332678213 7650750383743458249877165)
                  ·
                    refine ⟨2869031393903796843703937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7650750383743458249877165 2869031393903796843703937)
                    ·
                      refine ⟨2151773545427847632777953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2869031393903796843703937 2151773545427847632777953)
                      ·
                        rfl

theorem cell23_4190564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_4190564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190564 prefixEnd_4190564 := by exact prefixLift 4190564
  have htrace : WordTrace (prefixWord ++ tailWord_4190564) baseStart_4190564 baseEnd_4190564 := by
    simpa [prefixWord, tailWord_4190564, baseEnd_4190564] using wordTrace_append hprefix tailTrace_4190564
  have hstable : (prefixWord ++ tailWord_4190564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190564).length < 2 ^ (prefixWord ++ tailWord_4190564).sum := by decide
  have hdescent : baseEnd_4190564 < baseStart_4190564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190581 : List Nat := [1, 3, 4, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_4190581 : Nat := 118140960795 + 4190581 * 2 ^ 59
def prefixEnd_4190581 : Nat := 4983230072969 + 3 ^ 40 * 4190581 * 2
def baseEnd_4190581 : Nat := 2151782274598974066265375

theorem tailTrace_4190581 : CollatzResearch.WordTrace tailWord_4190581 prefixEnd_4190581 2151782274598974066265375 := by
  unfold tailWord_4190581
  simp only [CollatzResearch.WordTrace]
  refine ⟨152843045631248206100579597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101895363754165470733719731 152843045631248206100579597)
  ·
    refine ⟨57316142111718077287717349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152843045631248206100579597 57316142111718077287717349)
    ·
      refine ⟨10746776645947139491447003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57316142111718077287717349 10746776645947139491447003)
      ·
        refine ⟨16120164968920709237170505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10746776645947139491447003 16120164968920709237170505)
        ·
          refine ⟨12090123726690531927877879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16120164968920709237170505 12090123726690531927877879)
          ·
            refine ⟨18135185590035797891816819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12090123726690531927877879 18135185590035797891816819)
            ·
              refine ⟨27202778385053696837725229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18135185590035797891816819 27202778385053696837725229)
              ·
                refine ⟨10201041894395136314146961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27202778385053696837725229 10201041894395136314146961)
                ·
                  refine ⟨7650781420796352235610221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10201041894395136314146961 7650781420796352235610221)
                  ·
                    refine ⟨2869043032798632088353833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7650781420796352235610221 2869043032798632088353833)
                    ·
                      refine ⟨2151782274598974066265375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2869043032798632088353833 2151782274598974066265375)
                      ·
                        rfl

theorem cell23_4190581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_4190581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190581 prefixEnd_4190581 := by exact prefixLift 4190581
  have htrace : WordTrace (prefixWord ++ tailWord_4190581) baseStart_4190581 baseEnd_4190581 := by
    simpa [prefixWord, tailWord_4190581, baseEnd_4190581] using wordTrace_append hprefix tailTrace_4190581
  have hstable : (prefixWord ++ tailWord_4190581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190581).length < 2 ^ (prefixWord ++ tailWord_4190581).sum := by decide
  have hdescent : baseEnd_4190581 < baseStart_4190581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190587 : List Nat := [1, 1, 1, 1, 1, 8, 1, 2, 1, 6]
def baseStart_4190587 : Nat := 118140960795 + 4190587 * 2 ^ 59
def prefixEnd_4190587 : Nat := 4983230072969 + 3 ^ 40 * 4190587 * 2
def baseEnd_4190587 : Nat := 717261785160967014263449

theorem tailTrace_4190587 : CollatzResearch.WordTrace tailWord_4190587 prefixEnd_4190587 717261785160967014263449 := by
  unfold tailWord_4190587
  simp only [CollatzResearch.WordTrace]
  refine ⟨152843264469226469125298015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101895509646150979416865343 152843264469226469125298015)
  ·
    refine ⟨229264896703839703687947023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152843264469226469125298015 229264896703839703687947023)
    ·
      refine ⟨343897345055759555531920535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229264896703839703687947023 343897345055759555531920535)
      ·
        refine ⟨515846017583639333297880803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343897345055759555531920535 515846017583639333297880803)
        ·
          refine ⟨773769026375458999946821205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515846017583639333297880803 773769026375458999946821205)
          ·
            refine ⟨9067605777837410155626811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 773769026375458999946821205 9067605777837410155626811)
            ·
              refine ⟨13601408666756115233440217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9067605777837410155626811 13601408666756115233440217)
              ·
                refine ⟨10201056500067086425080163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13601408666756115233440217 10201056500067086425080163)
                ·
                  refine ⟨15301584750100629637620245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10201056500067086425080163 15301584750100629637620245)
                  ·
                    refine ⟨717261785160967014263449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15301584750100629637620245 717261785160967014263449)
                    ·
                      rfl

theorem cell23_4190587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 6].length) (baseStart_4190587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190587 prefixEnd_4190587 := by exact prefixLift 4190587
  have htrace : WordTrace (prefixWord ++ tailWord_4190587) baseStart_4190587 baseEnd_4190587 := by
    simpa [prefixWord, tailWord_4190587, baseEnd_4190587] using wordTrace_append hprefix tailTrace_4190587
  have hstable : (prefixWord ++ tailWord_4190587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190587).length < 2 ^ (prefixWord ++ tailWord_4190587).sum := by decide
  have hdescent : baseEnd_4190587 < baseStart_4190587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190604 : List Nat := [2, 2, 1, 2, 1, 4, 1, 4, 2, 4]
def baseStart_4190604 : Nat := 118140960795 + 4190604 * 2 ^ 59
def prefixEnd_4190604 : Nat := 4983230072969 + 3 ^ 40 * 4190604 * 2
def baseEnd_4190604 : Nat := 717264694884675825425923

theorem tailTrace_4190604 : CollatzResearch.WordTrace tailWord_4190604 prefixEnd_4190604 717264694884675825425923 := by
  unfold tailWord_4190604
  simp only [CollatzResearch.WordTrace]
  refine ⟨76421942255082440514333433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101895923006776587352444577 76421942255082440514333433)
  ·
    refine ⟨57316456691311830385750075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76421942255082440514333433 57316456691311830385750075)
    ·
      refine ⟨85974685036967745578625113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57316456691311830385750075 85974685036967745578625113)
      ·
        refine ⟨64481013777725809183968835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85974685036967745578625113 64481013777725809183968835)
        ·
          refine ⟨96721520666588713775953253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64481013777725809183968835 96721520666588713775953253)
          ·
            refine ⟨18135285124985383832991235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96721520666588713775953253 18135285124985383832991235)
            ·
              refine ⟨27202927687478075749486853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18135285124985383832991235 27202927687478075749486853)
              ·
                refine ⟨5100548941402139203028785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27202927687478075749486853 5100548941402139203028785)
                ·
                  refine ⟨3825411706051604402271589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5100548941402139203028785 3825411706051604402271589)
                  ·
                    refine ⟨717264694884675825425923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3825411706051604402271589 717264694884675825425923)
                    ·
                      rfl

theorem cell23_4190604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_4190604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190604 prefixEnd_4190604 := by exact prefixLift 4190604
  have htrace : WordTrace (prefixWord ++ tailWord_4190604) baseStart_4190604 baseEnd_4190604 := by
    simpa [prefixWord, tailWord_4190604, baseEnd_4190604] using wordTrace_append hprefix tailTrace_4190604
  have hstable : (prefixWord ++ tailWord_4190604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190604).length < 2 ^ (prefixWord ++ tailWord_4190604).sum := by decide
  have hdescent : baseEnd_4190604 < baseStart_4190604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190624 : List Nat := [2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 4]
def baseStart_4190624 : Nat := 118140960795 + 4190624 * 2 ^ 59
def prefixEnd_4190624 : Nat := 4983230072969 + 3 ^ 40 * 4190624 * 2
def baseEnd_4190624 : Nat := 2151804354267117398027677

theorem tailTrace_4190624 : CollatzResearch.WordTrace tailWord_4190624 prefixEnd_4190624 2151804354267117398027677 := by
  unfold tailWord_4190624
  simp only [CollatzResearch.WordTrace]
  refine ⟨76422306985046212222197463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101896409313394949629596617 76422306985046212222197463)
  ·
    refine ⟨114633460477569318333296195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76422306985046212222197463 114633460477569318333296195)
    ·
      refine ⟨171950190716353977499944293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114633460477569318333296195 171950190716353977499944293)
      ·
        refine ⟨32240660759316370781239555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171950190716353977499944293 32240660759316370781239555)
        ·
          refine ⟨48360991138974556171859333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32240660759316370781239555 48360991138974556171859333)
          ·
            refine ⟨9067685838557729282223625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48360991138974556171859333 9067685838557729282223625)
            ·
              refine ⟨6800764378918296961667719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9067685838557729282223625 6800764378918296961667719)
              ·
                refine ⟨10201146568377445442501579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6800764378918296961667719 10201146568377445442501579)
                ·
                  refine ⟨15301719852566168163752369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10201146568377445442501579 15301719852566168163752369)
                  ·
                    refine ⟨11476289889424626122814277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15301719852566168163752369 11476289889424626122814277)
                    ·
                      refine ⟨2151804354267117398027677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11476289889424626122814277 2151804354267117398027677)
                      ·
                        rfl

theorem cell23_4190624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_4190624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190624 prefixEnd_4190624 := by exact prefixLift 4190624
  have htrace : WordTrace (prefixWord ++ tailWord_4190624) baseStart_4190624 baseEnd_4190624 := by
    simpa [prefixWord, tailWord_4190624, baseEnd_4190624] using wordTrace_append hprefix tailTrace_4190624
  have hstable : (prefixWord ++ tailWord_4190624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190624).length < 2 ^ (prefixWord ++ tailWord_4190624).sum := by decide
  have hdescent : baseEnd_4190624 < baseStart_4190624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190645 : List Nat := [1, 3, 3, 2, 4, 1, 2, 1, 1, 1, 4]
def baseStart_4190645 : Nat := 118140960795 + 4190645 * 2 ^ 59
def prefixEnd_4190645 : Nat := 4983230072969 + 3 ^ 40 * 4190645 * 2
def baseEnd_4190645 : Nat := 2151815137360861815865081

theorem tailTrace_4190645 : CollatzResearch.WordTrace tailWord_4190645 prefixEnd_4190645 2151815137360861815865081 := by
  unfold tailWord_4190645
  simp only [CollatzResearch.WordTrace]
  refine ⟨152845379903016345030909389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101896919935344230020606259 152845379903016345030909389)
  ·
    refine ⟨57317017463631129386591021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152845379903016345030909389 57317017463631129386591021)
    ·
      refine ⟨21493881548861673519971633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57317017463631129386591021 21493881548861673519971633)
      ·
        refine ⟨16120411161646255139978725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21493881548861673519971633 16120411161646255139978725)
        ·
          refine ⟨3022577092808672838746011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16120411161646255139978725 3022577092808672838746011)
          ·
            refine ⟨4533865639213009258119017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022577092808672838746011 4533865639213009258119017)
            ·
              refine ⟨3400399229409756943589263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4533865639213009258119017 3400399229409756943589263)
              ·
                refine ⟨5100598844114635415383895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3400399229409756943589263 5100598844114635415383895)
                ·
                  refine ⟨7650898266171953123075843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5100598844114635415383895 7650898266171953123075843)
                  ·
                    refine ⟨11476347399257929684613765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7650898266171953123075843 11476347399257929684613765)
                    ·
                      refine ⟨2151815137360861815865081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11476347399257929684613765 2151815137360861815865081)
                      ·
                        rfl

theorem cell23_4190645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_4190645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190645 prefixEnd_4190645 := by exact prefixLift 4190645
  have htrace : WordTrace (prefixWord ++ tailWord_4190645) baseStart_4190645 baseEnd_4190645 := by
    simpa [prefixWord, tailWord_4190645, baseEnd_4190645] using wordTrace_append hprefix tailTrace_4190645
  have hstable : (prefixWord ++ tailWord_4190645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190645).length < 2 ^ (prefixWord ++ tailWord_4190645).sum := by decide
  have hdescent : baseEnd_4190645 < baseStart_4190645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
