Theory vfmTest1541[no_sig_docs]
Ancestors vfmTestDefs1541
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1541_0.nsv", "result1541_1.nsv", "result1541_2.nsv", "result1541_3.nsv", "result1541_4.nsv", "result1541_5.nsv", "result1541_6.nsv", "result1541_7.nsv", "result1541_8.nsv", "result1541_9.nsv", "result1541_10.nsv", "result1541_11.nsv", "result1541_12.nsv", "result1541_13.nsv", "result1541_14.nsv", "result1541_15.nsv"];
val thyn = "vfmTestDefs1541";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
