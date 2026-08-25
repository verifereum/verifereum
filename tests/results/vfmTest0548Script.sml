Theory vfmTest0548[no_sig_docs]
Ancestors vfmTestDefs0548
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0548_0.nsv"];
val thyn = "vfmTestDefs0548";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
