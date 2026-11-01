Theory vfmTest3036[no_sig_docs]
Ancestors vfmTestDefs3036
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3036_0.nsv", "result3036_1.nsv", "result3036_2.nsv", "result3036_3.nsv"];
val thyn = "vfmTestDefs3036";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
