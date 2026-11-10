Theory vfmTest3050[no_sig_docs]
Ancestors vfmTestDefs3050
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3050_0.nsv", "result3050_1.nsv", "result3050_2.nsv", "result3050_3.nsv"];
val thyn = "vfmTestDefs3050";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
