Theory vfmTest3013[no_sig_docs]
Ancestors vfmTestDefs3013
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3013_0.nsv", "result3013_1.nsv", "result3013_2.nsv", "result3013_3.nsv", "result3013_4.nsv"];
val thyn = "vfmTestDefs3013";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
