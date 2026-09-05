Theory vfmTest0654[no_sig_docs]
Ancestors vfmTestDefs0654
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0654_0.nsv", "result0654_1.nsv", "result0654_2.nsv"];
val thyn = "vfmTestDefs0654";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
