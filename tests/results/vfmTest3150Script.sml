Theory vfmTest3150[no_sig_docs]
Ancestors vfmTestDefs3150
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3150_0.nsv", "result3150_1.nsv", "result3150_2.nsv", "result3150_3.nsv", "result3150_4.nsv", "result3150_5.nsv", "result3150_6.nsv", "result3150_7.nsv"];
val thyn = "vfmTestDefs3150";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
