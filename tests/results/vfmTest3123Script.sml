Theory vfmTest3123[no_sig_docs]
Ancestors vfmTestDefs3123
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3123_0.nsv", "result3123_1.nsv", "result3123_2.nsv", "result3123_3.nsv", "result3123_4.nsv", "result3123_5.nsv"];
val thyn = "vfmTestDefs3123";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
