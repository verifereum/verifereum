Theory vfmTest3014[no_sig_docs]
Ancestors vfmTestDefs3014
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3014_0.nsv", "result3014_1.nsv", "result3014_2.nsv", "result3014_3.nsv", "result3014_4.nsv", "result3014_5.nsv", "result3014_6.nsv", "result3014_7.nsv"];
val thyn = "vfmTestDefs3014";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
