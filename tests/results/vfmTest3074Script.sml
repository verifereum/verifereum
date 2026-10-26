Theory vfmTest3074[no_sig_docs]
Ancestors vfmTestDefs3074
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3074_0.nsv", "result3074_1.nsv", "result3074_2.nsv", "result3074_3.nsv"];
val thyn = "vfmTestDefs3074";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
