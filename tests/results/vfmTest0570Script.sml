Theory vfmTest0570[no_sig_docs]
Ancestors vfmTestDefs0570
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0570_0.nsv", "result0570_1.nsv", "result0570_2.nsv", "result0570_3.nsv"];
val thyn = "vfmTestDefs0570";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
