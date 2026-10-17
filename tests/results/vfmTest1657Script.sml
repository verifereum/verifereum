Theory vfmTest1657[no_sig_docs]
Ancestors vfmTestDefs1657
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1657_0.nsv", "result1657_1.nsv", "result1657_2.nsv", "result1657_3.nsv", "result1657_4.nsv", "result1657_5.nsv", "result1657_6.nsv", "result1657_7.nsv", "result1657_8.nsv", "result1657_9.nsv", "result1657_10.nsv", "result1657_11.nsv", "result1657_12.nsv", "result1657_13.nsv", "result1657_14.nsv", "result1657_15.nsv", "result1657_16.nsv", "result1657_17.nsv", "result1657_18.nsv", "result1657_19.nsv"];
val thyn = "vfmTestDefs1657";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
