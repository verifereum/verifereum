Theory vfmTest2713[no_sig_docs]
Ancestors vfmTestDefs2713
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2713_0.nsv", "result2713_1.nsv", "result2713_2.nsv", "result2713_3.nsv", "result2713_4.nsv", "result2713_5.nsv", "result2713_6.nsv", "result2713_7.nsv", "result2713_8.nsv", "result2713_9.nsv", "result2713_10.nsv", "result2713_11.nsv", "result2713_12.nsv", "result2713_13.nsv", "result2713_14.nsv", "result2713_15.nsv", "result2713_16.nsv", "result2713_17.nsv", "result2713_18.nsv", "result2713_19.nsv", "result2713_20.nsv", "result2713_21.nsv", "result2713_22.nsv", "result2713_23.nsv"];
val thyn = "vfmTestDefs2713";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
