Theory vfmTest3041[no_sig_docs]
Ancestors vfmTestDefs3041
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3041_0.nsv", "result3041_1.nsv", "result3041_2.nsv", "result3041_3.nsv", "result3041_4.nsv", "result3041_5.nsv"];
val thyn = "vfmTestDefs3041";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
