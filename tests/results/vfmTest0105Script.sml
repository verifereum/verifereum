Theory vfmTest0105[no_sig_docs]
Ancestors vfmTestDefs0105
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0105_0.nsv", "result0105_1.nsv", "result0105_2.nsv"];
val thyn = "vfmTestDefs0105";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
