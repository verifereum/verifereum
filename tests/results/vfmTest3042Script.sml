Theory vfmTest3042[no_sig_docs]
Ancestors vfmTestDefs3042
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3042_0.nsv", "result3042_1.nsv", "result3042_2.nsv", "result3042_3.nsv"];
val thyn = "vfmTestDefs3042";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
