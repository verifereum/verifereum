Theory vfmTest3002[no_sig_docs]
Ancestors vfmTestDefs3002
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3002_0.nsv", "result3002_1.nsv", "result3002_2.nsv"];
val thyn = "vfmTestDefs3002";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
