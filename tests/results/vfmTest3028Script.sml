Theory vfmTest3028[no_sig_docs]
Ancestors vfmTestDefs3028
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3028_0.nsv", "result3028_1.nsv", "result3028_2.nsv", "result3028_3.nsv"];
val thyn = "vfmTestDefs3028";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
