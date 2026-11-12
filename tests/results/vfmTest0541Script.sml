Theory vfmTest0541[no_sig_docs]
Ancestors vfmTestDefs0541
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0541_0.nsv", "result0541_1.nsv", "result0541_2.nsv", "result0541_3.nsv", "result0541_4.nsv", "result0541_5.nsv", "result0541_6.nsv", "result0541_7.nsv", "result0541_8.nsv", "result0541_9.nsv"];
val thyn = "vfmTestDefs0541";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
