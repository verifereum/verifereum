Theory vfmTest0620[no_sig_docs]
Ancestors vfmTestDefs0620
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0620_0.nsv", "result0620_1.nsv"];
val thyn = "vfmTestDefs0620";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
