Theory vfmTest0239[no_sig_docs]
Ancestors vfmTestDefs0239
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0239_0.nsv", "result0239_1.nsv", "result0239_2.nsv", "result0239_3.nsv", "result0239_4.nsv"];
val thyn = "vfmTestDefs0239";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
