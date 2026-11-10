Theory vfmTest3131[no_sig_docs]
Ancestors vfmTestDefs3131
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3131_0.nsv", "result3131_1.nsv", "result3131_2.nsv"];
val thyn = "vfmTestDefs3131";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
