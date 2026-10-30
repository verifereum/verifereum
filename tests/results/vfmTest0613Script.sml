Theory vfmTest0613[no_sig_docs]
Ancestors vfmTestDefs0613
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0613_0.nsv", "result0613_1.nsv", "result0613_2.nsv"];
val thyn = "vfmTestDefs0613";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
