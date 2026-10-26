Theory vfmTest3026[no_sig_docs]
Ancestors vfmTestDefs3026
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3026_0.nsv", "result3026_1.nsv", "result3026_2.nsv", "result3026_3.nsv", "result3026_4.nsv", "result3026_5.nsv", "result3026_6.nsv", "result3026_7.nsv"];
val thyn = "vfmTestDefs3026";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
