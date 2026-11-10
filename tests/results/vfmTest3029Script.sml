Theory vfmTest3029[no_sig_docs]
Ancestors vfmTestDefs3029
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3029_0.nsv", "result3029_1.nsv", "result3029_2.nsv", "result3029_3.nsv"];
val thyn = "vfmTestDefs3029";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
