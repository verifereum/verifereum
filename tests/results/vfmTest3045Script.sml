Theory vfmTest3045[no_sig_docs]
Ancestors vfmTestDefs3045
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3045_0.nsv", "result3045_1.nsv", "result3045_2.nsv", "result3045_3.nsv", "result3045_4.nsv"];
val thyn = "vfmTestDefs3045";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
