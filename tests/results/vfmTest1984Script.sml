Theory vfmTest1984[no_sig_docs]
Ancestors vfmTestDefs1984
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1984_0.nsv", "result1984_1.nsv", "result1984_2.nsv", "result1984_3.nsv", "result1984_4.nsv", "result1984_5.nsv", "result1984_6.nsv", "result1984_7.nsv", "result1984_8.nsv", "result1984_9.nsv", "result1984_10.nsv", "result1984_11.nsv", "result1984_12.nsv", "result1984_13.nsv", "result1984_14.nsv", "result1984_15.nsv", "result1984_16.nsv", "result1984_17.nsv", "result1984_18.nsv", "result1984_19.nsv"];
val thyn = "vfmTestDefs1984";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
