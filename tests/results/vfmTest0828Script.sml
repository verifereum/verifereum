Theory vfmTest0828[no_sig_docs]
Ancestors vfmTestDefs0828
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0828_0.nsv", "result0828_1.nsv", "result0828_2.nsv"];
val thyn = "vfmTestDefs0828";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
