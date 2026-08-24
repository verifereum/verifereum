Theory vfmTest0325[no_sig_docs]
Ancestors vfmTestDefs0325
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0325_0.nsv", "result0325_1.nsv", "result0325_2.nsv", "result0325_3.nsv", "result0325_4.nsv", "result0325_5.nsv", "result0325_6.nsv", "result0325_7.nsv"];
val thyn = "vfmTestDefs0325";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
