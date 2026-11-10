Theory vfmTest3030[no_sig_docs]
Ancestors vfmTestDefs3030
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3030_0.nsv", "result3030_1.nsv", "result3030_2.nsv", "result3030_3.nsv"];
val thyn = "vfmTestDefs3030";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
