Theory vfmTest1303[no_sig_docs]
Ancestors vfmTestDefs1303
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1303_0.nsv", "result1303_1.nsv", "result1303_2.nsv", "result1303_3.nsv", "result1303_4.nsv", "result1303_5.nsv", "result1303_6.nsv", "result1303_7.nsv"];
val thyn = "vfmTestDefs1303";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
