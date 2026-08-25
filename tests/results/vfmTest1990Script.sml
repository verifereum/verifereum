Theory vfmTest1990[no_sig_docs]
Ancestors vfmTestDefs1990
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1990_0.nsv", "result1990_1.nsv", "result1990_2.nsv", "result1990_3.nsv", "result1990_4.nsv", "result1990_5.nsv", "result1990_6.nsv", "result1990_7.nsv", "result1990_8.nsv", "result1990_9.nsv", "result1990_10.nsv", "result1990_11.nsv", "result1990_12.nsv", "result1990_13.nsv", "result1990_14.nsv", "result1990_15.nsv", "result1990_16.nsv", "result1990_17.nsv", "result1990_18.nsv", "result1990_19.nsv"];
val thyn = "vfmTestDefs1990";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
