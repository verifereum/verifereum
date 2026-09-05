Theory vfmTest0713[no_sig_docs]
Ancestors vfmTestDefs0713
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0713_0.nsv", "result0713_1.nsv", "result0713_2.nsv", "result0713_3.nsv", "result0713_4.nsv", "result0713_5.nsv", "result0713_6.nsv", "result0713_7.nsv", "result0713_8.nsv"];
val thyn = "vfmTestDefs0713";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
