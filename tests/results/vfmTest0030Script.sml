Theory vfmTest0030[no_sig_docs]
Ancestors vfmTestDefs0030
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0030_0.nsv", "result0030_1.nsv", "result0030_2.nsv", "result0030_3.nsv", "result0030_4.nsv", "result0030_5.nsv", "result0030_6.nsv", "result0030_7.nsv", "result0030_8.nsv", "result0030_9.nsv"];
val thyn = "vfmTestDefs0030";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
