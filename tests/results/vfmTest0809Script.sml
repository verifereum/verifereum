Theory vfmTest0809[no_sig_docs]
Ancestors vfmTestDefs0809
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0809_0.nsv", "result0809_1.nsv", "result0809_2.nsv", "result0809_3.nsv", "result0809_4.nsv", "result0809_5.nsv", "result0809_6.nsv", "result0809_7.nsv"];
val thyn = "vfmTestDefs0809";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
