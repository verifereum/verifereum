Theory vfmTest1543[no_sig_docs]
Ancestors vfmTestDefs1543
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1543_0.nsv", "result1543_1.nsv", "result1543_2.nsv", "result1543_3.nsv", "result1543_4.nsv", "result1543_5.nsv", "result1543_6.nsv", "result1543_7.nsv", "result1543_8.nsv"];
val thyn = "vfmTestDefs1543";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
